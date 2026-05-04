#include <algorithm>
#include <cassert>
#include <cmath>
#include <chrono>
#include <iomanip>
#include <iostream>
#include <fstream>
#include <queue>
#include <random>
#include <set>
#include <sstream>
#include <stdexcept>
#include <string>
#include <unordered_map>
#include <unordered_set>
#include <vector>

struct SetCoverSolver {
 private:

  using Ans = std::pair<long long, std::vector<int>>;
  using Pair = std::pair<int, int>;
  using FSort = std::pair<double, int>;
  bool covered = false;
  int univ_size;
  int num_of_sets;
  int cPilotTime = 30;
  static const inline long long cInfty = 1E8;
  double alpha = 1;
  double alpha2 = 1;
  double beta = 1;
  double beta2 = 1;
  long long cur_ans_val;
  long long best_ans_val = cInfty;
  std::vector<bool> cur_ans;
  std::vector<bool> best_ans;
  std::vector<int> coverage;
  std::vector<int> set_costs;
  std::vector<double> harm_num;
  std::vector<std::set<int>> sets;
  std::unordered_set<std::string> pilot2_bans;

  struct PilotEl {
    long long cur_val;
    long double least_add;
    long double approx_val;
    long long max_val;
    std::vector<bool> mask;
    std::vector<int> looked;
    std::set<int> left;
  };

  static bool CompPilotEl(const PilotEl& first, const PilotEl& second) {
    return first.approx_val > second.approx_val;
  }

  void InputData(std::string& path) {
    std::ifstream input_file(path);
    input_file >> univ_size >> num_of_sets;
    set_costs.assign(num_of_sets, 0);
    sets.assign(num_of_sets, {});
    coverage.assign(univ_size, 0);
    std::string line;
    std::getline(input_file, line);
    for (int i = 0; i < num_of_sets; ++i) {
      std::getline(input_file, line);
      std::istringstream line_stream(line);
      line_stream >> set_costs[i];
      int element = 0;
      while (line_stream >> element) {
        sets[i].insert(element);
      }
    }
  }

  void OutputData(std::ostringstream& out) {
    if (best_ans_val == cInfty) {
      throw std::runtime_error("No answer found!");
    }
    out << best_ans_val << "\n";
    for (int i = 0; i < static_cast<int>(best_ans.size()); ++i) {
      if (best_ans[i]) {
        out << i << " ";
      }
    }
    out << "\n";
  }

  void FindAnsSoft() {
    cur_ans_val = 0;
    for (int i = 0; i < num_of_sets; ++i) {
      if (cur_ans[i]) {
        cur_ans_val += set_costs[i];
      }
    }
  }

  void SetBetter() {
    if (best_ans_val < cur_ans_val) {
      return;
    }
    best_ans_val = cur_ans_val;
    best_ans = cur_ans;
  }

  Ans GreedyEur(std::set<int> left, std::set<int> skip = {}) {
    if (left.empty()) {
      return {0, {}};
    }
    Ans ans = {0, {}};
    ans.second.reserve(num_of_sets);
    while (!left.empty()) {
      FSort best_set = {static_cast<double>(cInfty), -1};
      bool found = false;
      for (int i = 0; i < num_of_sets; ++i) {
        if (skip.count(i) > 0) {
          continue;
        }
        int inter_size = 0;
        if (sets[i].size() < left.size()) {
          for (auto iter = sets[i].begin(); iter != sets[i].end(); ++iter) {
            if (left.count(*iter) > 0) {
              ++inter_size;
            }
          }
        } else {
          for (auto iter = left.begin(); iter != left.end(); ++iter) {
            if (sets[i].count(*iter) > 0) {
              ++inter_size;
            }
          }
        }
        if (inter_size == 0) {
          skip.insert(i);
          continue;
        }
        double cur_value =
            static_cast<double>(set_costs[i]) / static_cast<double>(inter_size);
        if (!found || cur_value < best_set.first) {
          found = true;
          best_set = {cur_value, i};
        }
      }
      if (!found) {
        return {cInfty, {}};
      }
      int best_id = best_set.second;
      ans.first += set_costs[best_id];
      ans.second.push_back(best_id);
      skip.insert(best_id);
      for (auto iter = sets[best_id].begin(); iter != sets[best_id].end(); ++iter) {
        left.erase(*iter);
      }
    }
    return ans;
  }

  void AddSet(int ind) {
    if (cur_ans[ind]) {
      return;
    }
    cur_ans[ind] = true;
    for (auto iter = sets[ind].begin(); iter != sets[ind].end(); ++iter) {
      ++coverage[*iter];
    }
    cur_ans_val += set_costs[ind];
  }

  bool CanRem(int ind) {
    if (!cur_ans[ind]) {
      return false;
    }
    for (auto iter = sets[ind].begin(); iter != sets[ind].end(); ++iter) {
      if (coverage[*iter] < 2) {
        return false;
      }
    }
    return true;
  }

  bool RemSet(int ind) {
    if (!CanRem(ind)) {
      return false;
    }
    for (auto iter = sets[ind].begin(); iter != sets[ind].end(); ++iter) {
      --coverage[*iter];
      if (coverage[*iter] < 0) {
        throw std::logic_error("Impossible coverage!");
      }
    }
    cur_ans[ind] = false;
    cur_ans_val -= set_costs[ind];
    return true;
  }

  static bool Comp(Pair first, Pair second) {
    return (first.first < second.first) ||
           ((first.first == second.first) && (first.second < second.second));
  }

  void GreedyAlg() {
    std::set<int> left;
    for (int i = 0; i < univ_size; ++i) {
      left.insert(i);
    }
    Ans ans = GreedyEur(left, {});
    cur_ans_val = 0;
    for (size_t i = 0; i < ans.second.size(); ++i) {
      AddSet(ans.second[i]);
    }
    std::vector<Pair> sorted_sets;
    sorted_sets.reserve(ans.second.size());
    for (size_t i = 0; i < ans.second.size(); ++i) {
      int ind = ans.second[i];
      sorted_sets.push_back({set_costs[ind], ind});
    }
    std::sort(sorted_sets.begin(), sorted_sets.end(), Comp);
    for (int i = static_cast<int>(sorted_sets.size()) - 1; i >= 0; --i) {
      RemSet(sorted_sets[i].second);
    }
    covered = true;
    SetBetter();
  }

  void SetHarmNum() {
    harm_num.assign(univ_size + 1, 0);
    for (int i = 1; i <= univ_size; ++i) {
      harm_num[i] = harm_num[i - 1] + 1.0 / static_cast<double>(i);
    }
  }

  void TrySetBetter(const std::vector<int>& looked, const std::vector<bool>& mask,
                    const std::vector<int>& add_sets) {
    cur_ans.assign(num_of_sets, false);
    coverage.assign(univ_size, 0);
    cur_ans_val = 0;
    for (size_t i = 0; i < looked.size(); ++i) {
      if (mask[i]) {
        AddSet(looked[i]);
      }
    }
    for (size_t i = 0; i < add_sets.size(); ++i) {
      AddSet(add_sets[i]);
    }
    SetBetter();
  }

  void PilotMethod() {
    SetHarmNum();
    std::vector<FSort> order;
    order.reserve(num_of_sets);
    for (int i = 0; i < num_of_sets; ++i) {
      double cur = static_cast<double>(cInfty);
      if (!sets[i].empty()) {
        cur = static_cast<double>(set_costs[i]) /
              static_cast<double>(sets[i].size());
      }
      order.push_back({cur, i});
    }
    std::sort(order.begin(), order.end());
    std::priority_queue<PilotEl, std::vector<PilotEl>,
                        bool (*)(const PilotEl&, const PilotEl&)>
        heap(CompPilotEl);
    PilotEl root;
    root.cur_val = 0;
    root.max_val = best_ans_val;
    root.looked = {};
    root.mask = {};
    for (int i = 0; i < univ_size; ++i) {
      root.left.insert(i);
    }
    int root_h_ind = static_cast<int>(root.left.size());
    root.least_add = static_cast<long double>(root.max_val - root.cur_val) /
                     static_cast<long double>(harm_num[root_h_ind]);
    root.approx_val =
        static_cast<long double>(root.cur_val) +
        static_cast<long double>(root.max_val - root.cur_val) /
            (static_cast<long double>(alpha) *
             std::pow(static_cast<long double>(harm_num[root_h_ind]), beta));
    heap.push(root);
    auto start = std::chrono::steady_clock::now();
    while (!heap.empty()) {
      auto end = std::chrono::steady_clock::now();
      auto duration = std::chrono::duration_cast<std::chrono::seconds>(end - start);
      if (duration.count() > cPilotTime) {
        break;
      }
      PilotEl cur = heap.top();
      heap.pop();
      if (best_ans_val < static_cast<long long>(cur.cur_val + cur.least_add)) {
        continue;
      }
      if (static_cast<int>(cur.looked.size()) >= num_of_sets) {
        continue;
      }
      int pos = static_cast<int>(cur.looked.size());
      int set_id = order[pos].second;
      PilotEl take = cur;
      take.looked.push_back(set_id);
      take.mask.push_back(true);
      take.cur_val += set_costs[set_id];
      for (auto iter = sets[set_id].begin(); iter != sets[set_id].end(); ++iter) {
        take.left.erase(*iter);
      }
      std::set<int> take_skip(take.looked.begin(), take.looked.end());
      Ans take_greedy = GreedyEur(take.left, take_skip);
      if (take_greedy.first != cInfty) {
        take.max_val = take.cur_val + take_greedy.first;
        int h_ind = static_cast<int>(take.left.size());
        take.least_add = static_cast<long double>(take.max_val - take.cur_val) /
                         static_cast<long double>(harm_num[h_ind]);
        take.approx_val =
            static_cast<long double>(take.cur_val) +
            static_cast<long double>(take.max_val - take.cur_val) /
                (static_cast<long double>(alpha) *
                 std::pow(static_cast<long double>(harm_num[h_ind]), beta));
        if (take.max_val < best_ans_val) {
          TrySetBetter(take.looked, take.mask, take_greedy.second);
          covered = true;
        }
        if (!(best_ans_val < static_cast<long long>(take.cur_val + take.least_add))) {
          heap.push(take);
        }
      }
      PilotEl drop = cur;
      drop.looked.push_back(set_id);
      drop.mask.push_back(false);
      std::set<int> drop_skip(drop.looked.begin(), drop.looked.end());
      Ans drop_greedy = GreedyEur(drop.left, drop_skip);
      if (drop_greedy.first != cInfty) {
        drop.max_val = drop.cur_val + drop_greedy.first;
        int h_ind = static_cast<int>(drop.left.size());
        drop.least_add = static_cast<long double>(drop.max_val - drop.cur_val) /
                         static_cast<long double>(harm_num[h_ind]);
        drop.approx_val =
            static_cast<long double>(drop.cur_val) +
            static_cast<long double>(drop.max_val - drop.cur_val) /
                (static_cast<long double>(alpha) *
                 std::pow(static_cast<long double>(harm_num[h_ind]), beta));
        if (drop.max_val < best_ans_val) {
          TrySetBetter(drop.looked, drop.mask, drop_greedy.second);
          covered = true;
        }
        if (!(best_ans_val < static_cast<long long>(drop.cur_val + drop.least_add))) {
          heap.push(drop);
        }
      }
    }
  }

  double FindAverageCoverage() {
    if (coverage.empty()) {
      std::cout << 0 << "\n";
      return 0;
    }
    long long sum = 0;
    for (size_t i = 0; i < coverage.size(); ++i) {
      sum += coverage[i];
    }
    double avg = static_cast<double>(sum) / static_cast<double>(coverage.size());
    return avg;
  }

  void RemExtra() {
    cur_ans.assign(num_of_sets, false);
    coverage.assign(univ_size, 0);
    cur_ans_val = 0;
    for (int i = 0; i < num_of_sets; ++i) {
      if (best_ans[i]) {
        AddSet(i);
      }
    }
    std::vector<Pair> sorted_sets;
    for (int i = 0; i < num_of_sets; ++i) {
      if (cur_ans[i]) {
        sorted_sets.push_back({set_costs[i], i});
      }
    }
    std::sort(sorted_sets.begin(), sorted_sets.end(), Comp);
    for (int i = static_cast<int>(sorted_sets.size()) - 1; i >= 0; --i) {
      RemSet(sorted_sets[i].second);
    }
    SetBetter();
  }

  static std::string VecToString(const std::vector<int>& looked, const std::vector<bool>& mask) {
    std::vector<Pair> state;
    state.reserve(looked.size());
    for (size_t i = 0; i < looked.size(); ++i) {
      state.push_back({looked[i], static_cast<int>(mask[i])});
    }
    std::sort(state.begin(), state.end(), Comp);
    std::string result = "";
    for (size_t i = 0; i < state.size(); ++i) {
      if (i > 0) {
        result += ";";
      }
      result += std::to_string(state[i].first);
      result += ",";
      result += std::to_string(state[i].second);
    }
    return result;
  }

  void PilotMethod2() {
    SetHarmNum();
    std::priority_queue<PilotEl, std::vector<PilotEl>,
                        bool (*)(const PilotEl&, const PilotEl&)>
        heap(CompPilotEl);
    pilot2_bans.clear();
    PilotEl root;
    root.cur_val = 0;
    root.max_val = best_ans_val;
    for (int i = 0; i < univ_size; ++i) {
      root.left.insert(i);
    }
    int root_h_ind = static_cast<int>(root.left.size());
    root.least_add = static_cast<long double>(root.max_val - root.cur_val) /
                     static_cast<long double>(harm_num[root_h_ind]);
    root.approx_val =
        static_cast<long double>(root.cur_val) +
        static_cast<long double>(root.max_val - root.cur_val) /
            (static_cast<long double>(alpha2) *
             std::pow(static_cast<long double>(harm_num[root_h_ind]), beta2));
    pilot2_bans.insert(VecToString(root.looked, root.mask));
    heap.push(root);
    auto start = std::chrono::steady_clock::now();
    while (!heap.empty()) {
      auto end = std::chrono::steady_clock::now();
      auto duration = std::chrono::duration_cast<std::chrono::seconds>(end - start);
      if (duration.count() > cPilotTime) {
        break;
      }
      PilotEl cur = heap.top();
      heap.pop();
      if (best_ans_val < static_cast<long long>(cur.cur_val + cur.least_add)) {
        continue;
      }
      PilotEl base = cur;
      std::set<int> looked_set;
      for (size_t i = 0; i < base.looked.size(); ++i) {
        looked_set.insert(base.looked[i]);
      }
      int best_set = -1;
      double best_density = static_cast<double>(cInfty);
      for (int i = 0; i < num_of_sets; ++i) {
        if (looked_set.find(i) != looked_set.end()) {
          continue;
        }
        int inter_size = 0;
        if (sets[i].size() < base.left.size()) {
          for (auto iter = sets[i].begin(); iter != sets[i].end(); ++iter) {
            if (base.left.count(*iter) > 0) {
              ++inter_size;
            }
          }
        } else {
          for (auto iter = base.left.begin(); iter != base.left.end(); ++iter) {
            if (sets[i].count(*iter) > 0) {
              ++inter_size;
            }
          }
        }
        if (inter_size == 0) {
          base.looked.push_back(i);
          base.mask.push_back(false);
          looked_set.insert(i);
          continue;
        }
        double cur_density =
            static_cast<double>(set_costs[i]) / static_cast<double>(inter_size);
        if (best_set == -1 || cur_density < best_density) {
          best_set = i;
          best_density = cur_density;
        }
      }
      if (best_set == -1) {
        if (base.left.empty()) {
          TrySetBetter(base.looked, base.mask, {});
          covered = true;
        }
        continue;
      }
      PilotEl take = base;
      take.looked.push_back(best_set);
      take.mask.push_back(true);
      std::string take_key = VecToString(take.looked, take.mask);
      if (pilot2_bans.find(take_key) == pilot2_bans.end()) {
        pilot2_bans.insert(take_key);
        take.cur_val += set_costs[best_set];
        for (auto iter = sets[best_set].begin(); iter != sets[best_set].end(); ++iter) {
          take.left.erase(*iter);
        }
        std::set<int> take_skip(take.looked.begin(), take.looked.end());
        Ans take_greedy = GreedyEur(take.left, take_skip);
        if (take_greedy.first != cInfty) {
          take.max_val = take.cur_val + take_greedy.first;
          int h_ind = static_cast<int>(take.left.size());
          if (h_ind == 0) {
            take.least_add = 0;
            take.approx_val = static_cast<long double>(take.cur_val);
          } else {
            take.least_add = static_cast<long double>(take.max_val - take.cur_val) /
                             static_cast<long double>(harm_num[h_ind]);
            take.approx_val =
                static_cast<long double>(take.cur_val) +
                static_cast<long double>(take.max_val - take.cur_val) /
                    (static_cast<long double>(alpha2) *
                     std::pow(static_cast<long double>(harm_num[h_ind]), beta2));
          }
          if (take.max_val < best_ans_val) {
            TrySetBetter(take.looked, take.mask, take_greedy.second);
            covered = true;
          }
          if (!(best_ans_val < static_cast<long long>(take.cur_val + take.least_add))) {
            heap.push(take);
          }
        }
      }
      PilotEl drop = base;
      drop.looked.push_back(best_set);
      drop.mask.push_back(false);
      std::string drop_key = VecToString(drop.looked, drop.mask);
      if (pilot2_bans.find(drop_key) == pilot2_bans.end()) {
        pilot2_bans.insert(drop_key);
        std::set<int> drop_skip(drop.looked.begin(), drop.looked.end());
        Ans drop_greedy = GreedyEur(drop.left, drop_skip);
        if (drop_greedy.first != cInfty) {
          drop.max_val = drop.cur_val + drop_greedy.first;
          int h_ind = static_cast<int>(drop.left.size());
          if (h_ind == 0) {
            drop.least_add = 0;
            drop.approx_val = static_cast<long double>(drop.cur_val);
          } else {
            drop.least_add = static_cast<long double>(drop.max_val - drop.cur_val) /
                             static_cast<long double>(harm_num[h_ind]);
            drop.approx_val =
                static_cast<long double>(drop.cur_val) +
                static_cast<long double>(drop.max_val - drop.cur_val) /
                    (static_cast<long double>(alpha2) *
                     std::pow(static_cast<long double>(harm_num[h_ind]), beta2));
          }
          if (drop.max_val < best_ans_val) {
            TrySetBetter(drop.looked, drop.mask, drop_greedy.second);
            covered = true;
          }
          if (!(best_ans_val < static_cast<long long>(drop.cur_val + drop.least_add))) {
            heap.push(drop);
          }
        }
      }
    }
  }

 public:
  SetCoverSolver(std::string path, std::ostringstream& out) {
    InputData(path);
    cur_ans.resize(num_of_sets, false);
    GreedyAlg();
    alpha2 = std::min(FindAverageCoverage() / 5, double(1));
    PilotMethod2();
    RemExtra();
    alpha = std::min(FindAverageCoverage() / 5, double(1));
    PilotMethod();
    RemExtra();
    //std::cout << FindAverageCoverage() << "\n";
    OutputData(out);
  }
};
