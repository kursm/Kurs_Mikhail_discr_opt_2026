#include <algorithm>
#include <fstream>
#include <iostream>
#include <vector>
#include <set>
#include <sstream>
#include <stdexcept>
#include <string>
#include <tuple>

// std::string pathss = "./data/ks_4_0";

struct Objects {
  std::vector<int> cost;
  std::vector<int> wei;
  std::vector<int> ind;
  int num_of_obj;
  int max_wei;

  Objects () = default;

  Objects (Objects& other, std::vector<int>& rem_ind) {
    std::set<int> bad_ind;
    for (int i = 0; i < rem_ind.size(); ++i) {
      bad_ind.insert(rem_ind[i]);
    }
    long long sum_wei = 0;
    for (int i = 0; i < other.num_of_obj; ++i) {
      if (bad_ind.count(other.ind[i]) == 1) {
        sum_wei += other.wei[i];
      } else {
        cost.push_back(other.cost[i]);
        wei.push_back(other.wei[i]);
        ind.push_back(other.ind[i]);
      }
    }
    num_of_obj = cost.size();
    max_wei = other.max_wei - sum_wei;
    RemoveImp();
  }

  void RemoveImp() {
    static int uses = 0;
    std::vector<int> big_ind;
    for (size_t i = 0; i < num_of_obj; ++i) {
      if (wei[i] > max_wei) {
        big_ind.push_back(i);
      }
    }
    if (big_ind.empty()) {
      return;
    }
    ++uses;
    std::vector<int> cost_new;
    std::vector<int> wei_new;
    std::vector<int> ind_new;
    int i = -1;
    int j = 0;
    while (++i < cost.size()) {
      if (big_ind.size() < j) {
        continue;
      }
      if (big_ind[j] == i) {
        ++j;
        continue;
      }
      cost_new.push_back(cost[i]);
      wei_new.push_back(wei[i]);
      ind_new.push_back(ind[i]);
    }
    std::swap(cost, cost_new);
    std::swap(wei, wei_new);
    std::swap(ind, ind_new);
    num_of_obj = wei.size();
  }
};

struct Ans {
  long long sum_cost;
  std::vector<int> index;
};

Objects InpData(std::string path) {
  std::ifstream input_file(path);
  Objects ans;
  input_file >> ans.num_of_obj >> ans.max_wei;
  ans.cost.resize(ans.num_of_obj);
  ans.wei.resize(ans.num_of_obj);
  for (size_t i = 0; i < ans.num_of_obj; ++i) {
    input_file >> ans.cost[i] >> ans.wei[i];
    ans.ind.push_back(i);
  }
  return ans;
}

const long long cMaxMemory = 1LL << 27;

bool DpIsOk(Objects& obj) {
  return static_cast<long long>(obj.max_wei) *
         static_cast<long long>(obj.num_of_obj) <= cMaxMemory;
}

Ans DpAlg(Objects& obj) {
  if (!DpIsOk(obj)) {
    throw std::runtime_error("Dp Alg will work for too long and use too much!!!");
  }
  std::vector<std::vector<int>> max_cost(obj.num_of_obj + 1,
                                         std::vector<int>(obj.max_wei + 1, 0));
  long long debug = 0;
  for (int i = 1; i <= obj.num_of_obj; ++i) {
    for (int j = 1; j <= obj.max_wei; ++j) {
      if (obj.wei[i - 1] <= j) {
        max_cost[i][j] = std::max(max_cost[i - 1][j],
                                  max_cost[i - 1][j - obj.wei[i - 1]] +
                                  obj.cost[i - 1]);
      } else {
        max_cost[i][j] = max_cost[i - 1][j];
      }
      debug += max_cost[i][j];
    }
  }
  Ans ret;
  ret.sum_cost = max_cost[obj.num_of_obj][obj.max_wei];
  int indi = obj.num_of_obj;
  int indj = obj.max_wei;
  while ((indi > 0) && (indj > 0)) {
    if (max_cost[indi - 1][indj] != max_cost[indi][indj]) {
      ret.index.push_back(obj.ind[indi - 1]);
      indj -= obj.wei[indi - 1];
    }
    --indi;
  }
  return ret;
}

using Pair = std::pair<long double, int>;

bool Compare(Pair first, Pair second) {
  return first.first > second.first;
}

Ans GreedyPush(Objects& obj) {
  std::vector<Pair> den;
  den.reserve(obj.num_of_obj);
  for (int i = 0; i < obj.num_of_obj; ++i) {
    den.push_back(Pair(obj.cost[i] / obj.wei[i], i));
  }
  std::sort(den.begin(), den.end(), Compare);
  int cur_wei = 0;
  Ans ans;
  for (size_t i = 0; i < den.size(); ++i) {
    if (cur_wei + obj.wei[den[i].second] <= obj.max_wei) {
      ans.sum_cost += obj.cost[den[i].second];
      ans.index.push_back(obj.ind[den[i].second]);
    }
  }
  return ans;
}

Objects MakeObjByGcd(Objects& obj, int c) {
  Objects ans = obj;
  for (int i = 0; i < ans.num_of_obj; ++i) {
    if (ans.wei[i] % c != 0) {
      ans.wei[i] += c - (ans.wei[i] % c);
    }
    ans.wei[i] /= c;
  }
  ans.max_wei /= c;
  ans.RemoveImp();
  return ans;
}

std::vector<int> GcdEur(Objects& obj, int speed_log = 0) {
  if (DpIsOk(obj)) {
    return DpAlg(obj).index;
  }
  long long c = static_cast<long long>(obj.max_wei) *
                static_cast<long long>(obj.num_of_obj);
  c /= cMaxMemory;
  c /= (1 << speed_log);
  ++c;
  Objects new_obj = MakeObjByGcd(obj, c);
  Ans ans = DpAlg(new_obj);
  Objects left(obj, ans.index);
  if (left.max_wei > (1 << (speed_log + 1))) {
    std::vector<int> ans_also = GcdEur(left, speed_log + 1);
    for (int i = 0; i < ans_also.size(); ++i) {
      ans.index.push_back(ans_also[i]);
    }
    return ans.index;
  }
  std::vector<int> ans_also = GreedyPush(left).index;
  for (int i = 0; i < ans_also.size(); ++i) {
    ans.index.push_back(ans_also[i]);
  }
  return ans.index;
}

void BackPack(std::string path, std::ostringstream& out) {
  //std::ostream& out = std::cout;
  Objects obj = InpData(path);
  if (DpIsOk(obj)) {
    Ans ans = DpAlg(obj);
    out << ans.sum_cost << "\n";
    for (int i = 0; i < ans.index.size(); ++i) {
      out << ans.index[i] << " ";
    }
    out << "\nFull DP\n";
    return;
  }
  std::vector<int> index = GcdEur(obj);
  long long sum_cost = 0;
  for (size_t i = 0; i < index.size(); ++i) {
    sum_cost += obj.cost[index[i]];
  }
  out << sum_cost << "\n";
  for (size_t i = 0; i < index.size(); ++i) {
    out << index[i] << ' ';
  }
  out << "\n";
}