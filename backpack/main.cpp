#include <algorithm>
#include <fstream>
#include <iostream>
#include <vector>
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

  void RemoveImp() {
    std::vector<int> big_ind;
    for (size_t i = 0; i < num_of_obj; ++i) {

    }
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
  }
  return ans;
}

bool DpIsOk(Objects& obj) {
  const long long cMaxMemory = 1LL << 27;
  return static_cast<long long>(obj.max_wei) *
         static_cast<long long>(obj.num_of_obj) <= cMaxMemory;
}

Ans DpAlg(Objects& obj) {
  const long long cMaxMemory = 1LL << 27;
  if (static_cast<long long>(obj.max_wei) *
      static_cast<long long>(obj.num_of_obj) > cMaxMemory) {
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
      ret.index.push_back(indi - 1);
      indj -= obj.wei[indi - 1];
    }
    --indi;
  }
  return ret;
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
  out << "0 \n \n";
}