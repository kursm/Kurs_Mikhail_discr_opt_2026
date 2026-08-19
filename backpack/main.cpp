#include <algorithm>
#include <chrono>
#include <fstream>
#include <iostream>
#include <map>
#include <vector>
#include <set>
#include <sstream>
#include <stdexcept>
#include <string>
#include <tuple>
#include <random>
#include "coin/ClpSimplex.hpp"

struct BackpackSolver {
 private:

  using Pair = std::pair<long double, int>;
  std::vector<int> cost;
  std::vector<int> wei;
  std::vector<int> wei_greedy;
  std::vector<int> ones_taken;
  std::vector<bool> cur_taken;
  std::vector<bool> best_taken;
  std::vector<Pair> useful_sort;
  std::vector<int> rev_useful_sort;
  std::set<int> ind_active;
  std::vector<int> rem_tabu_list;
  std::vector<int> add_tabu_list;
  long long best_ans = 0;
  long long cur_ans;
  long long cMaxMemory = 1LL << 27;
  long long timer = 0;
  long long tabu_limit;
  double tabu_bad = 0.85;
  double add_alpha = 0.5;
  double alpha = 0.25;
  const double cEps = 1E-5;
  double is_one_after = 0.9;
  int num_of_obj;
  int max_wei;
  int greedy_max_wei;
  int cur_wei = 0;
  int cLp_iter = 500;
  int cMany = 3;
  int cRemPushIter = 500;
  int tabu_max_time = 1000;
  int tabu_max_iter = 500;
  int tabu_max_total = 500;
  bool is_accurate = false;

  struct Ans {
    long long sum_cost;
    std::vector<int> index;
  };

  void InpData(std::string path) {
    std::ifstream input_file(path);
    input_file >> num_of_obj >> max_wei;
    cost.resize(num_of_obj);
    wei.resize(num_of_obj);
    for (size_t i = 0; i < num_of_obj; ++i) {
      input_file >> cost[i] >> wei[i];
    }
  }

  bool DpIsOk() {
    return static_cast<long long>(max_wei) *
           static_cast<long long>(num_of_obj) <= cMaxMemory;
  }

  Ans DpAlg() {
    if (!DpIsOk()) {
      throw std::runtime_error("Dp Alg will work for too long and use too much memory!!!");
    }
    std::vector<std::vector<int>> max_cost(num_of_obj + 1,
                                           std::vector<int>(max_wei + 1, 0));
    for (int i = 1; i <= num_of_obj; ++i) {
      for (int j = 1; j <= max_wei; ++j) {
        if (wei[i - 1] <= j) {
          max_cost[i][j] = std::max(max_cost[i - 1][j],
                                    max_cost[i - 1][j - wei[i - 1]] +
                                    cost[i - 1]);
        } else {
          max_cost[i][j] = max_cost[i - 1][j];
        }
      }
    }
    Ans ret;
    ret.sum_cost = max_cost[num_of_obj][max_wei];
    int indi = num_of_obj;
    int indj = max_wei;
    while ((indi > 0) && (indj > 0)) {
      if (max_cost[indi - 1][indj] != max_cost[indi][indj]) {
        ret.index.push_back(indi - 1);
        indj -= wei[indi - 1];
      }
      --indi;
    }
    return ret;
  }

  Ans GreedyDp() {
    std::vector<std::vector<int>> max_cost(
        ind_active.size() + 1, std::vector<int>(greedy_max_wei + 1, 0));
    int i = 0;
    std::vector<int> decode;
    decode.reserve(ind_active.size());
    for (auto it = ind_active.begin(); it != ind_active.end(); ++it) {
      ++i;
      decode.push_back(*it);
      for (int j = 1; j <= greedy_max_wei; ++j) {
        if (wei_greedy[*it] <= j) {
          max_cost[i][j] = std::max(max_cost[i - 1][j],
                                    max_cost[i - 1][j - wei_greedy[*it]] +
                                    cost[*it]);
        } else {
          max_cost[i][j] = max_cost[i - 1][j];
        }
      }
    }
    Ans ret;
    ret.sum_cost = max_cost[ind_active.size()][greedy_max_wei];
    int indi = ind_active.size();
    int indj = greedy_max_wei;
    while ((indi > 0) && (indj > 0)) {
      if (max_cost[indi - 1][indj] != max_cost[indi][indj]) {
        ret.index.push_back(decode[indi - 1]);
        indj -= wei_greedy[decode[indi - 1]];
      }
      --indi;
    }
    return ret;
  }

  void MakeObjByGcd(long long c) {
    if (wei_greedy.size() != num_of_obj) {
      wei_greedy.resize(num_of_obj);
    }
    for (int i = 0; i < num_of_obj; ++i) {
      wei_greedy[i] = wei[i];
      if (wei_greedy[i] % c != 0) {
        wei_greedy[i] += c - (wei_greedy[i] % c);
      }
      wei_greedy[i] /= c;
    }
    greedy_max_wei = (max_wei - cur_wei) / c;
  }

  bool AddEl(int index) {
    if (cur_taken[index]) {
      return false;
    }
    if (cur_wei + wei[index] > max_wei) {
      return false;
    }
    cur_taken[index] = true;
    cur_wei += wei[index];
    cur_ans += cost[index];
    return true;
  }

  bool RemEl(int index) {
    if (!cur_taken[index]) {
      return false;
    }
    cur_taken[index] = false;
    cur_wei -= wei[index];
    cur_ans -= cost[index];
    return true;
  }

  bool CanAdd(int index) {
    if (cur_taken[index]) {
      return false;
    }
    if (cur_wei + wei[index] > max_wei) {
      return false;
    }
    return true;
  }

  bool IsTabuBlocked(int index) const {
    return timer <= static_cast<long long>(rem_tabu_list[index]) + tabu_max_time;
  }

  bool CanAddJustOne(int i1, int i2) {
    if ((cur_taken[i1]) || (cur_taken[i2])) {
      return false;
    }
    if ((cur_wei + wei[i1] <= max_wei) &&
        (cur_wei + wei[i2] <= max_wei) &&
        (cur_wei + wei[i1] + wei[i2] > max_wei)) {
      return true;
    }
    return false;
  }

  static bool Comp(Pair& first, Pair& second) {
    return first.first > second.first;
  }

  int ApplyEffective(Ans& ans) {
    std::vector<Pair> profit;
    for (size_t i = 0; i < ans.index.size(); ++i) {
      profit.push_back(Pair(double(cost[ans.index[i]]) / wei[ans.index[i]], i));
    }
    std::sort(profit.begin(), profit.end(), Comp);
    int num = ans.index.size();
    num = static_cast<int>(static_cast<double>(num) * alpha + 1);
    if (num > ans.index.size()) {
      num = ans.index.size();
    }
    for (int i = 0; i < num; ++i) {
      AddEl(ans.index[profit[i].second]);
    }
    return num;
  }

  int OneGcdEur(long long gcd) {
    MakeObjByGcd(gcd);
    ind_active.clear();
    for (int i = 0; i < num_of_obj; ++i) {
      if (cur_taken[i]) {
        continue;
      }
      if (IsTabuBlocked(i)) {
        continue;
      }
      if (wei_greedy[i] > greedy_max_wei) {
        continue;
      }
      ind_active.insert(i);
    }
    Ans ans = GreedyDp();
    int outp = 0;
    if (gcd > 1) {
      return ApplyEffective(ans);
    }
    for (size_t i = 0; i < ans.index.size(); ++i) {
      if (AddEl(ans.index[i])) {
        ++outp;
      } else {
        throw std::runtime_error("Something strange!");
      }
    }
    return outp;
  }

  bool TimeToMult(std::vector<int>& logs) {
    if (logs.size() < 5) {
      return false;
    }
    for (int i = 0; i < 5; ++i) {
      if (logs[logs.size() - i - 1] != 1) {
        return false;
      }
    }
    return true;
  }

  bool TimeToBreak(std::vector<int>& logs) {
    if (logs.size() < 20) {
      return false;
    }
    for (int i = 0; i < 4; ++i) {
      if (logs[logs.size() - 5 * i - 1] != 2) {
        return false;
      }
    }
    return true;
  }

  void GcdEur() {
    auto start = std::chrono::steady_clock::now();
    long long c = static_cast<long long>(max_wei) *
                  static_cast<long long>(num_of_obj);
    c /= cMaxMemory;
    ++c;
    long long d = c;
    std::vector<int> logs;
    while (true) {
      int added = OneGcdEur(d);
      if (added > 0) {
        c = static_cast<long long>(max_wei - cur_wei) *
            static_cast<long long>(num_of_obj);
        c /= cMaxMemory;
        ++c;
        d = c;
        logs.push_back(0);
        continue;
      }
      ++d;
      logs.push_back(1);
      if (TimeToMult(logs)) {
        d *= 2;
        logs.push_back(2);
        if (ind_active.empty()) {
          break;
        }
        if (TimeToBreak(logs)) {
          break;
        }
      }
      if (d > max_wei) {
        break;
      }
      auto end = std::chrono::steady_clock::now();
      auto duration = std::chrono::duration_cast<std::chrono::seconds>(end - start);
      if (duration.count() > 120) {
        break;
      }
    }
  }

  void FindAns() {
    cur_ans = 0;
    for (size_t i = 0; i < num_of_obj; ++i) {
      cur_ans += cost[i] * static_cast<int>(cur_taken[i]);
    }
  }

  void SetBetter() {
    if (cur_ans > best_ans) {
      best_taken = cur_taken;
      best_ans = cur_ans;
    }
  }

  void AddInitial(ClpSimplex& model) {
    std::vector<int> index(num_of_obj);
    std::vector<double> weight_cond(num_of_obj);
    for (int i = 0; i < num_of_obj; ++i) {
      index[i] = i;
      weight_cond[i] = wei[i];
    }
    model.addRow(num_of_obj, index.data(), weight_cond.data(), -COIN_DBL_MAX, max_wei);
  }

  void AccurateFound(std::vector<int>& non_zero) {
    for (int i = 0; i < num_of_obj; ++i) {
      cur_taken[i] = false;
    }
    cur_ans = 0;
    cur_wei = 0;
    for (size_t i = 0; i < non_zero.size(); ++i) {
      cur_taken[non_zero[i]] = true;
      cur_ans += cost[non_zero[i]];
      cur_wei += wei[non_zero[i]];
    }
    SetBetter();
    is_accurate = true;
  }

  void GetSol(std::vector<int>& non_zero, std::vector<double>& value, int non_one) {
    for (int i = 0; i < num_of_obj; ++i) {
      cur_taken[i] = false;
    }
    ones_taken.clear();
    cur_ans = 0;
    cur_wei = 0;
    std::vector<Pair> for_sort;
    for (size_t i = 0; i < non_zero.size(); ++i) {
      if (value[i] > is_one_after) {
        if (AddEl(non_zero[i])) {
          ones_taken.push_back(non_zero[i]);
        }
      }
      if (non_one < 2) {
        for_sort.push_back(Pair(double(cost[non_zero[i]]) /
                                double(wei[non_zero[i]]), i));
      }
    }
    if (non_one < 2) {
      std::sort(for_sort.begin(), for_sort.end(), Comp);
      for (size_t i = 0; i < for_sort.size(); ++i) {
        AddEl(non_zero[for_sort[i].second]);
      }
    }
    SetBetter();
  }

  void AddCond(std::vector<int>& non_zero, ClpSimplex& model) {
    int size = non_zero.size();
    std::vector<int> index(size);
    std::vector<double> weight_cond(size, 1.0);
    for (int i = 0; i < size; ++i) {
      index[i] = non_zero[i];
    }
    model.addRow(size, index.data(), weight_cond.data(), -COIN_DBL_MAX, size - 1);
  }

  bool IsNotPushible(std::vector<int>& non_zero) {
    bool is_addable = false;
    for (int i = 0; i < num_of_obj; ++i) {
      if (CanAdd(i)) {
        is_addable = false;
      }
    }
    return true;
  }

  static std::string VecToStr(std::vector<int>& vec) {
    std::string result;
    for (size_t i = 0; i < vec.size(); ++i) {
        if (i > 0) result += ",";
        result += std::to_string(vec[i]);
    }
    return result;
  }

  void AddCleverCond(std::vector<int>& non_zero, std::vector<double>& value,
                     ClpSimplex& model) {
    if (IsNotPushible(non_zero)) {
      FindAns();
      SetBetter();
      int size = non_zero.size();
      std::vector<int> index(size);
      std::vector<double> weight_cond(size, 1.0);
      for (int i = 0; i < size; ++i) {
        index[i] = non_zero[i];
      }
      model.addRow(size, index.data(), weight_cond.data(), -COIN_DBL_MAX, size - 2);
    }
    if (static_cast<long long>(max_wei - cur_wei) * num_of_obj < cMaxMemory) {
      OneGcdEur(1);
      SetBetter();
      int size = ones_taken.size();
      std::vector<double> weight_cond(size, 1.0);
      model.addRow(size, ones_taken.data(), weight_cond.data(), -COIN_DBL_MAX, size - 1);
    } else {
      bool brake = false;
      for (int i = 0; i < non_zero.size(); ++i) {
        for (int j = i + 1; j < non_zero.size(); ++j) {
          if ((value[i] > 0.2) && (value[j] > 0.2) &&
              (std::abs(value[i] + value[j] - 1) < cEps)) {
            int i1 = i;
            int j1 = j;
            if (value[i1] < value[j1]) {
              std::swap(i1, j1);
            }
            if (AddEl(non_zero[i1])) {
              long long value = static_cast<long long>(max_wei - cur_wei) * num_of_obj;
              if (value < cMaxMemory) {
                OneGcdEur(1);
                SetBetter();
                int size = ones_taken.size() + 1;
                std::vector<double> weight_cond(size, 1.0);
                ones_taken.push_back(non_zero[i1]);
                model.addRow(size, ones_taken.data(), weight_cond.data(), -COIN_DBL_MAX, size - 1);
                ones_taken.pop_back();
              }
              RemEl(non_zero[i1]);
            }
          }
        }
      }
    }
  }

  bool IsSame(double* prev_ans, double* ans) {
    for (int i = 0; i < num_of_obj; ++i) {
      if (std::abs(prev_ans[i] - ans[i]) > cEps) {
        return false;
      }
    }
    return true;
  }

  void DecreaseSeriously(std::vector<int>& non_zero, ClpSimplex& model, int how) {
    int size = non_zero.size();
    std::vector<int> index(size);
    std::vector<double> weight_cond(size, 1.0);
    for (int i = 0; i < size; ++i) {
      index[i] = non_zero[i];
    }
    model.addRow(size, index.data(), weight_cond.data(), -COIN_DBL_MAX, size - how - 1);
  }

  void SolveCheckAndAdd(ClpSimplex& model) {
    std::map<std::string, int> seen;
    double* prev_ans = nullptr;
    for (int i = 0; i < cLp_iter; ++i) {
      model.dual();
      double* ans = model.primalColumnSolution();
      std::vector<int> non_zero;
      std::vector<double> value;
      int non_one_count = 0;
      int sum_wei = 0;
      for (int i = 0; i < num_of_obj; ++i) {
        if (ans[i] > cEps) {
          non_zero.push_back(i);
          value.push_back(ans[i]);
          sum_wei += wei[i];
          if (ans[i] < is_one_after) {
            ++non_one_count;
          }
        }
      }
      if (sum_wei <= max_wei) {
        AccurateFound(non_zero);
        break;
      }
      GetSol(non_zero, value, non_one_count);
      if (prev_ans == nullptr) {
        AddCond(non_zero, model);
      } else {
        if (IsSame(prev_ans, ans)) {
          AddCleverCond(non_zero, value, model);
          std::string problem = VecToStr(non_zero);
          if (seen.count(problem) == 1) {
            ++seen[problem];
          } else {
            seen[problem] = 1;
          }
          if (seen[problem] % cMany == 0) {
            DecreaseSeriously(non_zero, model, seen[problem] / cMany);
          }
        } else {
          AddCond(non_zero, model);
        }
      }
      prev_ans = ans;
    }
  }

  void LpSolve() {
    ClpSimplex  model;
    model.setLogLevel(0);
    std::vector<double> cost_m(num_of_obj);
    std::vector<double> lower(num_of_obj, 0);
    std::vector<double> upper(num_of_obj, 1);
    for (size_t i = 0; i < num_of_obj; ++i) {
      cost_m[i] = -cost[i];
    }
    model.resize(0, num_of_obj);
    for (int j = 0; j < num_of_obj; ++j) {
      model.setObjectiveCoefficient(j, cost_m[j]);
      model.setColumnLower(j, lower[j]);
      model.setColumnUpper(j, upper[j]);
    }
    AddInitial(model);
    SolveCheckAndAdd(model);
  }

  bool SwapObj(int i1, int i2, bool sure = false) {
    if (cur_taken[i1] && cur_taken[i2]) {
      return false;
    }
    if (!(cur_taken[i1] || cur_taken[i2])) {
      return false;
    }
    if (!cur_taken[i1]) {
      std::swap(i1, i2);
    }
    if (cur_wei - wei[i1] + wei[i2] > max_wei) {
      return false;
    }
    int profit = cost[i2] - cost[i1];
    if (sure && (profit > 0)) {
      cur_wei = cur_wei - wei[i1] + wei[i2];
      cur_taken[i1] = false;
      cur_taken[i2] = true;
      return true;
    }
    return false;
  }

  void SetBestAsCur() {
    cur_ans = best_ans;
    cur_taken = best_taken;
    cur_wei = 0;
    for (int i = 0; i < num_of_obj; ++i) {
      if (cur_taken[i]) {
        cur_wei += wei[i];
      }
    }
  }

  void SetUsefulSort() {
    useful_sort.reserve(num_of_obj);
    for (int i = 0; i < num_of_obj; ++i) {
      useful_sort.push_back(Pair(
        static_cast<double>(cost[i]) / static_cast<double>(wei[i]), i));
    }
    std::sort(useful_sort.begin(), useful_sort.end(), Comp);
  }

  void SetReverseUseful() {
    rev_useful_sort.assign(num_of_obj, -1);
    for (int pos = 0; pos < num_of_obj; ++pos) {
      int index = useful_sort[pos].second;
      if ((index >= 0) && (index < num_of_obj)) {
        rev_useful_sort[index] = pos;
      } else {
        throw std::runtime_error("Cringe sort");
      }
    }
  }

  Ans PushByEur(int div = 1) {
    long long value = num_of_obj;
    std::vector<bool> cur_taken_copy = cur_taken;
    long long cur_ans_copy = cur_ans;
    int cur_wei_copy = cur_wei;
    value *= (max_wei - cur_wei);
    int i = 0;
    while (value > cMaxMemory) {
      if (i >= (num_of_obj / div)) {
        break;
      }
      if (cur_taken[useful_sort[i].second]) {
        ++i;
        continue;
      }
      if (IsTabuBlocked(useful_sort[i].second)) {
        ++i;
        continue;
      }
      if (AddEl(useful_sort[i].second)) {
        ++i;
        value = num_of_obj;
        value *= (max_wei - cur_wei);
        continue;
      }
      ++i;
    }
    OneGcdEur(1);
    Ans ans;
    ans.sum_cost = 0;
    for (int i = 0; i < num_of_obj; ++i) {
      if (cur_taken[i] && (!cur_taken_copy[i])) {
        ans.index.push_back(i);
        ans.sum_cost += cost[i];
      }
    }
    std::swap(cur_ans, cur_ans_copy);
    std::swap(cur_taken, cur_taken_copy);
    std::swap(cur_wei_copy, cur_wei);
    return ans;
  }

  void ApplyAns(const Ans& ans) {
    for (size_t i = 0; i < ans.index.size(); ++i) {
      AddEl(ans.index[i]);
    }
  }

  int RemoveAndPush(int div = 1) {
    int iter = 0;
    for (; iter < cRemPushIter; ++iter) {
      bool changed = false;
      for (int i = 0; i < num_of_obj; ++i) {
        if (!cur_taken[i]) {
          continue;
        }
        RemEl(i);
        Ans ans = PushByEur(div);
        if (ans.sum_cost > cost[i]) {
          ApplyAns(ans);
          SetBetter();
          changed = true;
          break;
        } else {
          AddEl(i);
        }
      }
      if (!changed) {
        break;
      }
    }
    return iter;
  }

  bool OneRemoveTabuOper(std::vector<int>& perm, int div = 1) {
    bool changed_any = false;
    for (int iter = 0; iter < tabu_max_iter; ++iter) {
      bool changed = false;
      for (size_t p = 0; p < perm.size(); ++p) {
        int i = perm[p];
        if (!cur_taken[i]) {
          continue;
        }
        long long before = cur_ans;
        RemEl(i);
        bool not_often = rem_tabu_list[i] < (timer - tabu_max_time);
        int old_tabu_time = rem_tabu_list[i];
        long long old_timer = timer;
        rem_tabu_list[i] = static_cast<int>(timer);
        ++timer;
        Ans ans = PushByEur(div);
        long long candidate = before - cost[i] + ans.sum_cost;
        if (ans.sum_cost > cost[i]) {
          ApplyAns(ans);
          changed = true;
          changed_any = true;
          SetBetter();
          break;
        }
        if (ans.sum_cost < cost[i]) {
          bool not_too_bad =
              static_cast<double>(candidate) >= tabu_bad * static_cast<double>(best_ans);
          if (not_too_bad && not_often) {
            ApplyAns(ans);
            changed = true;
            changed_any = true;
            SetBetter();
            break;
          }
        }
        AddEl(i);
        rem_tabu_list[i] = old_tabu_time;
        timer = old_timer;
      }
      if (!changed) {
        //std::cout << "Iter is: " << iter << "\n";
        //break;
      }
    }
    return changed_any;
  }

  void GreedyOnCurWei(int left) {
    if ((left < 0) || (left >= num_of_obj)) {
      return;
    }
    std::vector<int> taken;
    for (int i = 0; i < num_of_obj; ++i) {
      if (!cur_taken[i]) {
        continue;
      }
      if (i == left) {
        continue;
      }
      taken.push_back(i);
      RemEl(i);
    }
    cur_taken[left] = true;
    cur_ans = cost[left];
    cur_wei = wei[left];
    std::vector<int> add_order;
    add_order.reserve(taken.size());
    for (size_t i = 0; i < taken.size(); ++i) {
      int pos = rev_useful_sort[taken[i]];
      if ((pos >= 0) && (pos < num_of_obj)) {
        add_order.push_back(pos);
      } else {
        throw std::runtime_error("Incorrect pos!");
      }
    }
    std::sort(add_order.begin(), add_order.end());
    for (size_t i = 0; i < add_order.size(); ++i) {
      AddEl(useful_sort[add_order[i]].second);
    }
  }

  bool OneAddTabuOper(std::vector<int>& perm) {
    bool changed_any = false;
    for (int iter = 0; iter < tabu_max_iter; ++iter) {
      bool changed = false;
      for (size_t p = 0; p < perm.size(); ++p) {
        int i = perm[p];
        if ((i < 0) || (i >= num_of_obj)) {
          continue;
        }
        if (cur_taken[i]) {
          continue;
        }
        std::vector<bool> cur_taken_copy = cur_taken;
        long long cur_ans_copy = cur_ans;
        int cur_wei_copy = cur_wei;
        if (!AddEl(i)) {
          cur_taken[i] = true;
          cur_ans += cost[i];
          cur_wei += wei[i];
          if (cur_wei > max_wei) {
            GreedyOnCurWei(i);
          }
        }
        bool accepted = false;
        if (cur_ans > best_ans) {
          accepted = true;
          SetBetter();
        } else {
          bool not_too_bad =
              static_cast<double>(cur_ans) >= tabu_bad * static_cast<double>(best_ans);
          bool not_often = add_tabu_list[i] < (timer - tabu_max_time);
          if (not_too_bad && not_often) {
            accepted = true;
          }
        }
        if (accepted) {
          add_tabu_list[i] = static_cast<int>(timer);
          ++timer;
          changed = true;
          changed_any = true;
        } else {
          std::swap(cur_taken, cur_taken_copy);
          std::swap(cur_ans, cur_ans_copy);
          std::swap(cur_wei, cur_wei_copy);
        }
      }
      if (!changed) {
        break;
      }
    }
    return changed_any;
  }

  void TabuSearch(int div = 1) {
    std::vector<int> perm(num_of_obj);
    for (int i = 0; i < num_of_obj; ++i) {
      perm[i] = i;
    }
    std::random_device rd;
    std::mt19937 gen(rd());
    std::uniform_real_distribution<double> dist(0.0, 1.0);
    tabu_limit = best_ans;
    auto start = std::chrono::steady_clock::now();
    for (int restart = 0; restart < tabu_max_total; ++restart) {
      std::shuffle(perm.begin(), perm.end(), gen);
      bool changed = false;
      if (dist(gen) < add_alpha) {
        changed = OneAddTabuOper(perm);
        if (!changed) {
          changed = OneRemoveTabuOper(perm, div);
        }
      } else {
        changed = OneRemoveTabuOper(perm, div);
        if (!changed) {
          changed = OneAddTabuOper(perm);
        }
      }
      if (!changed) {
        break;
      }
      auto end = std::chrono::steady_clock::now();
      auto duration = std::chrono::duration_cast<std::chrono::seconds>(end - start);
      if (duration.count() > 10) {
        break;
      }
    }
  }

  void SetRandomSolution() {
    for (int i = 0; i < num_of_obj; ++i) {
      cur_taken[i] = false;
    }
    cur_ans = 0;
    cur_wei = 0;
    std::random_device rd;
    std::mt19937 gen(rd());
    std::uniform_real_distribution<double> dist(0.0, 1.0);
    for (int i = 0; i < num_of_obj; ++i) {
      if (dist(gen) > 0.75) {
        AddEl(useful_sort[i].second);
      }
    }
    SetBetter();
  }

  void SetTabuMaxIter() {
    tabu_max_iter = 0;
    for (int i = 0; i < num_of_obj; ++i) {
      if (cur_taken[i]) {
        ++tabu_max_iter;
      }
    }
    tabu_max_iter *= 2;
  }

  void LocalSearch() {
    SetUsefulSort();
    SetReverseUseful();
    auto start = std::chrono::steady_clock::now();
    int times = 0;
    while(true) {
      for (add_alpha = 0.9; add_alpha > 0.05; add_alpha -= 0.3) {
        for (tabu_bad = 0.9; tabu_bad > 0.05; tabu_bad -= 0.3) {
          SetBestAsCur();
          SetTabuMaxIter();
          long long copy = best_ans;
          RemoveAndPush(times + 1);
          SetBetter();
          SetBestAsCur();
          TabuSearch(times + 1);
          RemoveAndPush(times + 1);
          SetBetter();
        }
      }
      auto end = std::chrono::steady_clock::now();
      auto duration = std::chrono::duration_cast<std::chrono::seconds>(end - start);
      if (duration.count() > 20) {
        break;
      }
      times = duration.count() / 30;
    }
  }

 public:
  BackpackSolver(std::string path, std::ostringstream& out) {
    InpData(path);
    rem_tabu_list.resize(num_of_obj, -tabu_max_time - 10);
    add_tabu_list.resize(num_of_obj, -tabu_max_time - 10);
    cur_taken.resize(num_of_obj, false);
    cur_ans = 0;
    //Solution 1
    if (DpIsOk()) {
      Ans ans = DpAlg();
      out << ans.sum_cost << "\n";
      for (int i = 0; i < ans.index.size(); ++i) {
        out << ans.index[i] << " ";
      }
      out << "\nFull DP\n";
      return;
    }
    GcdEur();
    FindAns();
    SetBetter();
    //End of Sol 1

    //Solution 2 and 3
    LpSolve();
    LocalSearch();
    //End of Sol 2 and 3
    
    out << best_ans << "\n";
    for (size_t i = 0; i < num_of_obj; ++i) {
      if (best_taken[i]) {
        out << i << ' ';
      }
    }
    out << "\n";
  }
};
