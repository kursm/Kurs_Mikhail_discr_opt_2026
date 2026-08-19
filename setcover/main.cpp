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
  int cPilotTime = 20;
  int cTwoAddTime = 500;
  int cAnnealingTime = 15;
  int cTries = 1000;
  double cAnnealingLow = 30;
  double cAnnealingMed = 40;
  double cAnnealingHigh = 30;
  static const inline long long cInfty = 1E8;
  double add_prob = 0.7;
  double alpha = 1;
  double alpha2 = 1;
  double beta = 1;
  double beta2 = 1;
  double temp_alpha = 100;
  double temp_beta = 1;
  double temp_num = 0.5;
  long double temp;
  long double temp_change = 0.9999;
  long double temp_delta = 0.995;
  long double temp_stop = 1E-8;
  long long cur_ans_val;
  long long best_ans_val = cInfty;
  std::vector<bool> cur_ans;
  std::vector<bool> best_ans;
  std::vector<int> coverage;
  std::vector<int> set_costs;
  std::vector<int> cost_order;
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
    if (!covered) {
      throw std::runtime_error("Set is not covered!");
    }
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
      FSort best_set = {cInfty, -1};
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
      double cur = cInfty;
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
      int set_id = order[cur.looked.size()].second;
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
        size_t h_ind = take.left.size();
        take.least_add = static_cast<long double>(take.max_val - take.cur_val) /
                         static_cast<long double>(harm_num[h_ind]);
        take.approx_val =
            static_cast<long double>(take.cur_val) +
            static_cast<long double>(take.max_val - take.cur_val) /
                (static_cast<long double>(alpha) *
                 std::pow(static_cast<long double>(harm_num[h_ind]), beta));
        if (take.max_val < best_ans_val) {
          TrySetBetter(take.looked, take.mask, take_greedy.second);
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
        size_t h_ind = drop.left.size();
        drop.least_add = static_cast<long double>(drop.max_val - drop.cur_val) /
                         static_cast<long double>(harm_num[h_ind]);
        drop.approx_val =
            static_cast<long double>(drop.cur_val) +
            static_cast<long double>(drop.max_val - drop.cur_val) /
                (static_cast<long double>(alpha) *
                 std::pow(static_cast<long double>(harm_num[h_ind]), beta));
        if (drop.max_val < best_ans_val) {
          TrySetBetter(drop.looked, drop.mask, drop_greedy.second);
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
      double best_density = cInfty;
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
          }
          if (!(best_ans_val < static_cast<long long>(drop.cur_val + drop.least_add))) {
            heap.push(drop);
          }
        }
      }
    }
  }

  void SetCostOrder() {
    cost_order.clear();
    std::vector<Pair> sorted_sets;
    sorted_sets.reserve(num_of_sets);
    for (size_t i = 0; i < num_of_sets; ++i) {
      sorted_sets.push_back({set_costs[i], i});
    }
    std::sort(sorted_sets.begin(), sorted_sets.end(), Comp);
    cost_order.reserve(num_of_sets);
    for (int i = sorted_sets.size() - 1; i > -1; --i) {
      cost_order.push_back(sorted_sets[i].second);
    }
  }

  long long OneAdd(int which) {
    if (cur_ans[which]) {
      return 0;
    }
    long long ans = set_costs[which];
    AddSet(which);
    for (size_t i = 0; i < cost_order.size(); ++i) {
      int ind = cost_order[i];
      if (ind == which) {
        continue;
      }
      if (RemSet(ind)) {
        ans -= set_costs[ind];
      }
    }
    return ans;
  }

  bool ManyOneAdd() {
    bool any_change = false;
    while (true) {
      bool changed = false;
      for (int i = 0; i < num_of_sets; ++i) {
        std::vector<bool> cur_ans_copy = cur_ans;
        std::vector<int> coverage_copy = coverage;
        long long cur_ans_val_copy = cur_ans_val;
        long long ans = OneAdd(i);
        if (ans < 0) {
          any_change = true;
          changed = true;
          break;
        }
        std::swap(cur_ans, cur_ans_copy);
        std::swap(coverage, coverage_copy);
        std::swap(cur_ans_val, cur_ans_val_copy);
      }
      if (!changed) {
        break;
      }
    }
    return any_change;
  }

  void RemSetSure(int ind) {
    if (!cur_ans[ind]) {
      return;
    }
    if (!CanRem(ind)) {
      covered = false;
    }
    for (auto iter = sets[ind].begin(); iter != sets[ind].end(); ++iter) {
      --coverage[*iter];
      if (coverage[*iter] < 0) {
        throw std::logic_error("Impossible coverage!");
      }
    }
    cur_ans[ind] = false;
    cur_ans_val -= set_costs[ind];
    return;
  }

  long long OneRem(int ind) {
    if (!cur_ans[ind]) {
      return 0;
    }
    RemSetSure(ind);
    std::set<int> left;
    for (int i = 0; i < univ_size; ++i) {
      if (coverage[i] <= 0) {
        left.insert(i);
      }
    }
    std::set<int> skip;
    skip.insert(ind);
    for (int i = 0; i < num_of_sets; ++i) {
      if (cur_ans[i]) {
        skip.insert(i);
      }
    }
    Ans add_ans = GreedyEur(left, skip);
    if (add_ans.first < set_costs[ind]) {
      for (size_t i = 0; i < add_ans.second.size(); ++i) {
        AddSet(add_ans.second[i]);
      }
      covered = true;
      return add_ans.first - set_costs[ind];
    }
    AddSet(ind);
    covered = true;
    return 0;
  }

  bool ManyOneRem() {
    bool any_change = false;
    while (true) {
      bool changed = false;
      for (int i = 0; i < num_of_sets; ++i) {
        long long ans = OneRem(i);
        if (ans < 0) {
          any_change = true;
          changed = true;
          break;
        }
      }
      if (!changed) {
        break;
      }
    }
    return any_change;
  }

  long long TwoAdd(int first, int second) {
    long long ans = set_costs[first] + set_costs[second];
    AddSet(first);
    AddSet(second);
    for (size_t i = 0; i < cost_order.size(); ++i) {
      int ind = cost_order[i];
      if ((ind == first) || (ind == second)) {
        continue;
      }
      if (RemSet(ind)) {
        ans -= set_costs[ind];
      }
    }
    return ans;
  }

  bool ManyTwoAdd() {
    bool any_change = false;
    auto start = std::chrono::steady_clock::now();
    while (true) {
      bool changed = false;
      for (int first_pos = cost_order.size() - 1; first_pos >= 0; --first_pos) {
        int i = cost_order[first_pos];
        if (cur_ans[i]) {
          continue;
        }
        for (int second_pos = first_pos - 1; second_pos >= 0; --second_pos) {
          auto end = std::chrono::steady_clock::now();
          auto duration = std::chrono::duration_cast<std::chrono::seconds>(end - start);
          if (duration.count() > 10) {
            break;
          }
          int j = cost_order[second_pos];
          if (cur_ans[j]) {
            continue;
          }
          std::vector<bool> cur_ans_copy = cur_ans;
          std::vector<int> coverage_copy = coverage;
          long long cur_ans_val_copy = cur_ans_val;
          long long ans = TwoAdd(i, j);
          if (ans < 0) {
            any_change = true;
            changed = true;
            break;
          }
          std::swap(cur_ans, cur_ans_copy);
          std::swap(coverage, coverage_copy);
          std::swap(cur_ans_val, cur_ans_val_copy);
        }
        if (changed) {
          break;
        }
      }
      if (!changed) {
        break;
      }
    }
    return any_change;
  }

  bool ManyTwoRandomAdd() {
    bool any_change = false;
    std::random_device rd;
    std::mt19937 gen(rd());
    std::uniform_int_distribution<int> dist(0, num_of_sets - 1);
    auto start = std::chrono::steady_clock::now();
    while (true) {
      auto end = std::chrono::steady_clock::now();
      auto duration = std::chrono::duration_cast<std::chrono::milliseconds>(end - start);
      if (duration.count() >= cTwoAddTime) {
        break;
      }
      int first = dist(gen);
      int second = dist(gen);
      if (first == second) {
        continue;
      }
      if (cur_ans[first] || cur_ans[second]) {
        continue;
      }
      std::vector<bool> cur_ans_copy = cur_ans;
      std::vector<int> coverage_copy = coverage;
      long long cur_ans_val_copy = cur_ans_val;
      long long ans = TwoAdd(first, second);
      if (ans < 0) {
        any_change = true;
      } else {
        std::swap(cur_ans, cur_ans_copy);
        std::swap(coverage, coverage_copy);
        std::swap(cur_ans_val, cur_ans_val_copy);
      }
    }
    return any_change;
  }

  void LocalSearch() {
    while(true) {
      bool succes_add = ManyOneAdd();
      succes_add = succes_add || ManyTwoRandomAdd();
      bool succes_rem = ManyOneRem();
      if ((!succes_add) && (!succes_rem)) {
        break;
      }
    }
    SetBetter();
  }

  double MeasureOneAdd() {
    std::vector<bool> cur_ans_copy = cur_ans;
    std::vector<int> coverage_copy = coverage;
    long long cur_ans_val_copy = cur_ans_val;
    std::random_device rd;
    std::mt19937 gen(rd());
    std::uniform_int_distribution<int> dist(0, num_of_sets - 1);
    long long total_microseconds = 0;
    for (int iter = 0; iter < 10; ++iter) {
      int which = dist(gen);
      int misses = 0;
      while (cur_ans[which]) {
        which = dist(gen);
        ++misses;
        if (misses > cTries) {
          throw std::runtime_error("Not able to find an el!");
        }
      }
      auto start = std::chrono::steady_clock::now();
      OneAdd(which);
      auto end = std::chrono::steady_clock::now();
      auto duration =
          std::chrono::duration_cast<std::chrono::microseconds>(end - start);
      total_microseconds += duration.count();
    }
    cur_ans = cur_ans_copy;
    coverage = coverage_copy;
    cur_ans_val = cur_ans_val_copy;
    return static_cast<double>(total_microseconds) / 10.0;
  }

  double MeasureOneRemAnnealing() {
    std::vector<bool> cur_ans_copy = cur_ans;
    std::vector<int> coverage_copy = coverage;
    long long cur_ans_val_copy = cur_ans_val;
    std::random_device rd;
    std::mt19937 gen(rd());
    std::uniform_int_distribution<int> dist(0, num_of_sets - 1);
    long long total_microseconds = 0;
    for (int iter = 0; iter < 10; ++iter) {
      int which = dist(gen);
      int misses = 0;
      while (!cur_ans[which]) {
        which = dist(gen);
        ++misses;
        if (misses > cTries) {
          std::vector<int> taken_sets;
          for (int i = 0; i < num_of_sets; ++i) {
            if (cur_ans[i]) {
              taken_sets.push_back(i);
            }
          }
          std::uniform_int_distribution<int> taken_dist(
              0, static_cast<int>(taken_sets.size()) - 1);
          which = taken_sets[taken_dist(gen)];
          break;
        }
      }
      auto start = std::chrono::steady_clock::now();
      OneRemAnnealing(which);
      auto end = std::chrono::steady_clock::now();
      auto duration =
          std::chrono::duration_cast<std::chrono::microseconds>(end - start);
      total_microseconds += duration.count();
    }
    cur_ans = cur_ans_copy;
    coverage = coverage_copy;
    cur_ans_val = cur_ans_val_copy;
    return static_cast<double>(total_microseconds) / 10.0;
  }

  void SetTemperature() {
    /*double add_time = MeasureOneAdd();
    double rem_time = MeasureOneRemAnnealing();
    double avg_time = add_time * add_prob + rem_time * (1 - add_prob);
    long double ann_low_steps = cAnnealingLow * double(1000000.0) / avg_time;
    long double ann_med_steps = cAnnealingMed * double(1000000.0) / avg_time;
    long double ann_high_steps = cAnnealingHigh * double(1000000.0) / avg_time;
    long double q_log = (std::log(-std::log(static_cast<long double>(0.8))) -
                         std::log(-std::log(static_cast<long double>(0.2)))) /
                        ann_med_steps;
    if (q_log < std::log(static_cast<long double>(0.99999))) {
      q_log = std::log(static_cast<long double>(0.99999));
    }
    temp_change = std::exp(q_log);
    long double avg_delta = std::pow(double(best_ans_val) / 10, 0.5);
    long double temp_med_start = -avg_delta / std::log(static_cast<long double>(0.01));
    long double temp_beg = temp_med_start / std::exp(q_log * ann_low_steps);
    temp = temp_beg;
    long double temp_med_finish = -avg_delta / std::log(static_cast<long double>(0.9));
    long double temp_end = temp_med_finish * std::exp(q_log * ann_high_steps);
    temp_stop = temp_end;*/
    long double avg_delta = std::pow(double(best_ans_val) / 10, 0.5);
    temp_change = 0.9999;
    if (num_of_sets > 2000) {
      temp_change = 0.9992;
    }
    temp = avg_delta * 15 * std::pow(num_of_sets * univ_size, 0.33);
    temp_stop = avg_delta / (30 * std::pow(num_of_sets * univ_size, 0.25));
    /*temp = temp_alpha * std::pow(static_cast<double>(best_ans_val), temp_beta);
    temp *= std::pow(static_cast<double>(num_of_sets), temp_num);
    if (univ_size > 2000) {
      temp_delta = 0.999;
    }*/
  }

  void SetFastTemperature() {
    long double avg_delta = std::pow(double(best_ans_val) / 10, 0.5);
    temp_change = 0.995;
    if (num_of_sets > 2000) {
      temp_change = 0.95;
    }
    temp = avg_delta * 1 * std::pow(num_of_sets * univ_size, 0.33);
    temp_stop = avg_delta / (6 * std::pow(num_of_sets * univ_size, 0.25));
  }

  bool OneRemAnnealing(int ind) {
    if (!cur_ans[ind]) {
      return false;
    }
    RemSetSure(ind);
    std::set<int> left;
    for (int i = 0; i < univ_size; ++i) {
      if (coverage[i] <= 0) {
        left.insert(i);
      }
    }
    std::set<int> skip;
    skip.insert(ind);
    for (int i = 0; i < num_of_sets; ++i) {
      if (cur_ans[i]) {
        skip.insert(i);
      }
    }
    Ans add_ans = GreedyEur(left, skip);
    if (add_ans.first < set_costs[ind]) {
      for (size_t i = 0; i < add_ans.second.size(); ++i) {
        AddSet(add_ans.second[i]);
      }
      covered = true;
      return true;
    }
    if (add_ans.first != cInfty && temp > 0) {
      long long delta = add_ans.first - set_costs[ind];
      double accept_prob = std::exp(-static_cast<double>(delta) / temp);
      static std::random_device rd;
      static std::mt19937 gen(rd());
      static std::uniform_real_distribution<double> prob_dist(0.0, 1.0);
      if (prob_dist(gen) < accept_prob) {
        for (size_t i = 0; i < add_ans.second.size(); ++i) {
          AddSet(add_ans.second[i]);
        }
        covered = true;
        return true;
      }
    }
    AddSet(ind);
    covered = true;
    return false;
  }

  void Annealing(bool fast = false) {
    auto start = std::chrono::steady_clock::now();
    int counter = 0;
    std::random_device rd;
    std::mt19937 gen(rd());
    std::uniform_int_distribution<int> dist(0, num_of_sets - 1);
    std::uniform_real_distribution<double> prob_dist(0.0, 1.0);
    if (fast) {
      SetFastTemperature();
    } else {
      SetTemperature();
    }
    //std::cout << "Anneal counter " << counter << ", temp on final: " << temp << "\n";
    while(true) {
      ++counter;
      auto end = std::chrono::steady_clock::now();
      auto duration = std::chrono::duration_cast<std::chrono::seconds>(end - start);
      if (duration.count() >= cAnnealingTime) {
        temp *= temp_delta;
        //std::cout << ".";
      }
      if (temp <= temp_stop) {
        break;
      }
      if (prob_dist(gen) < add_prob) {
        std::vector<bool> cur_ans_copy = cur_ans;
        std::vector<int> coverage_copy = coverage;
        long long cur_ans_val_copy = cur_ans_val;
        int which = dist(gen);
        int misses = 0;
        while (cur_ans[which]) {
          which = dist(gen);
          ++misses;
          if (misses > cTries) {
            throw std::runtime_error("Not able to find an el!");
          }
        }
        long long delta = OneAdd(which);
        bool accept = false;
        if (delta < 0) {
          accept = true;
          SetBetter();
        } else {
          double accept_prob = std::exp(-static_cast<double>(delta) / temp);
          if (prob_dist(gen) < accept_prob) {
            accept = true;
          }
        }
        if (!accept) {
          std::swap(cur_ans, cur_ans_copy);
          std::swap(coverage, coverage_copy);
          std::swap(cur_ans_val, cur_ans_val_copy);
        }
      } else {
        int which = dist(gen);
        int misses = 0;
        while (!cur_ans[which]) {
          which = dist(gen);
          ++misses;
          if (misses > cTries) {
            std::vector<int> taken_sets;
            for (int i = 0; i < num_of_sets; ++i) {
              if (cur_ans[i]) {
                taken_sets.push_back(i);
              }
            }
            std::uniform_int_distribution<int> taken_dist(0,
                static_cast<int>(taken_sets.size()) - 1);
            which = taken_sets[taken_dist(gen)];
            break;
          }
        }
        OneRemAnnealing(which);
      }
      temp *= temp_change;
    }
    SetBetter();
    //std::cout << "Anneal counter " << counter << "temp on final: " << temp << "\n";
  }

  void SetRandomStart() {
    for (int i = 0; i < num_of_sets; ++i) {
      AddSet(i);
    }
    std::vector<int> perm(num_of_sets);
    for (int i = 0; i < num_of_sets; ++i) {
      perm[i] = i;
    }
    std::random_device rd;
    std::mt19937 gen(rd());
    std::shuffle(perm.begin(), perm.end(), gen);
    for (int i = 0; i < num_of_sets; ++i) {
      RemSet(perm[i]);
    }
  }

  void SomeAnnealing() {
    std::vector<bool> start_cur_ans = cur_ans;
    std::vector<int> start_coverage = coverage;
    long long start_cur_ans_val = cur_ans_val;
    std::vector<bool> best_local_ans = cur_ans;
    std::vector<int> best_local_coverage = coverage;
    long long best_local_val = cur_ans_val;
    int max_iter = 10;
    if (num_of_sets > 2000) {
      max_iter = 6;
    }
    if (univ_size < 50) {
      max_iter = 20;
    }
    for (int iter = 0; iter < max_iter; ++iter) {
      cur_ans = start_cur_ans;
      coverage = start_coverage;
      cur_ans_val = start_cur_ans_val;
      //SetRandomStart();
      Annealing();
      if (cur_ans_val < best_local_val) {
        best_local_ans = cur_ans;
        best_local_coverage = coverage;
        best_local_val = cur_ans_val;
      }
      cur_ans = start_cur_ans;
      coverage = start_coverage;
      cur_ans_val = start_cur_ans_val;
    }
    cur_ans = best_local_ans;
    coverage = best_local_coverage;
    cur_ans_val = best_local_val;
  }

  void SetBestAsCur() {
    cur_ans.assign(num_of_sets, false);
    coverage.assign(univ_size, 0);
    cur_ans_val = 0;
    for (int i = 0; i < num_of_sets; ++i) {
      if (best_ans[i]) {
        AddSet(i);
      }
    }
  }

  void FindHamDist() {
    int ham_dist = 0;
    for (int i = 0; i < num_of_sets; ++i) {
      if (best_ans[i] != cur_ans[i]) {
        ++ham_dist;
      }
    }
    std::ofstream logs("logs.txt", std::ios::app);
    logs << ham_dist << "\n";
  }

  void LNS() {
    auto start = std::chrono::steady_clock::now();
    std::random_device rd;
    std::mt19937 gen(rd());
    while (true) {
      auto now = std::chrono::steady_clock::now();
      auto duration = std::chrono::duration_cast<std::chrono::seconds>(now - start);
      if (duration.count() >= 30) {
        break;
      }
      SetBestAsCur();
      Annealing(true);
      std::vector<int> cur_only;
      std::vector<int> best_only;
      for (int i = 0; i < num_of_sets; ++i) {
        if (cur_ans[i] && !best_ans[i]) {
          cur_only.push_back(i);
        }
        if (best_ans[i] && !cur_ans[i]) {
          best_only.push_back(i);
        }
      }
      std::vector<bool> cur_ans_backup = cur_ans;
      std::vector<int> coverage_backup = coverage;
      long long cur_ans_val_backup = cur_ans_val;
      for (int rep = 0; rep < 30; ++rep) {
        cur_ans = cur_ans_backup;
        coverage = coverage_backup;
        cur_ans_val = cur_ans_val_backup;
        std::shuffle(cur_only.begin(), cur_only.end(), gen);
        std::shuffle(best_only.begin(), best_only.end(), gen);
        int rem_pos = 0;
        int add_pos = 0;
        while ((rem_pos < static_cast<int>(cur_only.size())) ||
               (add_pos < static_cast<int>(best_only.size()))) {
          while (rem_pos < static_cast<int>(cur_only.size())) {
            if (RemSet(cur_only[rem_pos])) {
              long long log_best_ans = best_ans_val;
              SetBetter();
              if (best_ans_val != log_best_ans) {
                std::cout  << "Done something\n";
              }
              ++rem_pos;
            } else {
              AddSet(best_only[add_pos]);
              ++add_pos;
            }
          }
        }
        cur_ans = cur_ans_backup;
        coverage = coverage_backup;
        cur_ans_val = cur_ans_val_backup;
      }
    }
  }

 public:
  SetCoverSolver(std::string path, std::ostringstream& out) {
    InputData(path);
    cur_ans.resize(num_of_sets, false);
    GreedyAlg();

    /* // FIRST SOLUTION
    alpha2 = std::min(FindAverageCoverage() / 5, double(1));
    PilotMethod2();
    RemExtra();
    alpha = std::min(FindAverageCoverage() / 5, double(1));
    PilotMethod();
    RemExtra();*/

    // SECOND SOLUTION
    SetCostOrder();
    LocalSearch();
    SomeAnnealing();
    SetBestAsCur();
    LocalSearch();
    
    /* THIRD SOLUTION
    LocalSearch();
    LNS();
    LocalSearch();
    alpha2 = std::min(FindAverageCoverage() / 5, double(1));
    PilotMethod2();
    RemExtra();
    alpha = std::min(FindAverageCoverage() / 5, double(1));
    PilotMethod();
    RemExtra();*/
    //std::cout << FindAverageCoverage() << "\n";
    OutputData(out);
  }
};
