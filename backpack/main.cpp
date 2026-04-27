#include <algorithm>
#include <chrono>
#include <fstream>
#include <iostream>
#include <vector>
#include <set>
#include <sstream>
#include <stdexcept>
#include <string>
#include <tuple>
#include "coin/ClpSimplex.hpp"
#include "coin/CoinHelperFunctions.hpp"
#include "coin/CoinTime.hpp"
#include "coin/CoinBuild.hpp"
#include "coin/CoinModel.hpp"

struct BackpackSolver {
 private:

  std::vector<int> cost;
  std::vector<int> wei;
  std::vector<int> wei_greedy;
  std::vector<bool> cur_taken;
  std::vector<bool> best_taken;
  std::set<int> ind_active;
  long long best_ans = 0;
  long long cur_ans;
  long long cMaxMemory = 1LL << 27;
  int num_of_obj;
  int max_wei;
  int greedy_max_wei;
  int cur_wei = 0;
  using Pair = std::pair<long double, int>;

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

  int OneGcdEur(long long gcd) {
    MakeObjByGcd(gcd);
    ind_active.clear();
    for (int i = 0; i < num_of_obj; ++i) {
      if (cur_taken[i]) {
        continue;
      }
      if (wei_greedy[i] > greedy_max_wei) {
        continue;
      }
      ind_active.insert(i);
    }
    Ans ans = GreedyDp();
    int outp = 0;
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
      if (d == 1) {
        break;
      }
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
        if (TimeToBreak(logs)) {
          break;
        }
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

 public:
  BackpackSolver(std::string path, std::ostringstream& out) {
    InpData(path);
    if (DpIsOk()) {
      Ans ans = DpAlg();
      out << ans.sum_cost << "\n";
      for (int i = 0; i < ans.index.size(); ++i) {
        out << ans.index[i] << " ";
      }
      out << "\nFull DP\n";
      return;
    }
    cur_taken.resize(num_of_obj, false);
    cur_ans = 0;
    GcdEur();
    FindAns();
    SetBetter();
    out << best_ans << "\n";
    for (size_t i = 0; i < num_of_obj; ++i) {
      if (best_taken[i]) {
        out << i << ' ';
      }
    }
    out << "\n";
  }
};