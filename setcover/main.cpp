#include <iostream>
#include <fstream>
#include <set>
#include <sstream>
#include <stdexcept>
#include <string>
#include <vector>

//std::string path = "Setcover/data/sc_10000_2";
const int cInfty = 10000000;

std::vector<int> StringToInt(std::string str) {
  std::string int_str;
  std::vector<int> ans; 
  for (size_t i = 0; i < str.size(); ++i) {
    if ((str[i] == ' ') || (str[i] == '\n')) {
      if (int_str.size() > 0) {
        ans.push_back(std::stoi(int_str));
      }
      int_str = "";
    }
    else {
      int_str = int_str + str[i];
    }
  }
  if (int_str.size() > 0) {
    ans.push_back(std::stoi(int_str));
  }
  return ans;
}

struct Set {
  std::set<int> uncovered;
  std::vector<std::set<int>> sets;
  std::vector<int> set_costs;
  std::vector<int> set_index;
  int num_of_sets;

  Set (int n, std::vector<std::string> lines) {
    for (int i = 0; i < n; ++i) {
      uncovered.insert(i);
    }
    for (size_t i = 0; i < lines.size(); ++i) {
      std::vector<int> inp = StringToInt(lines[i]);
      sets.push_back(std::set<int>());
      set_costs.push_back(inp[0]);
      set_index.push_back(set_index.size());
      for (int j = 1; j < inp.size(); ++j) {
        sets.back().insert(inp[j]);
      }
    }
    num_of_sets = sets.size();
  }

  Set (Set& otherset, int added) {
    uncovered = otherset.uncovered;
    for (auto iter = otherset.sets[added].begin();
      iter != otherset.sets[added].end(); ++iter) {
      uncovered.erase(*iter);
    }
    for (size_t i = 0; i < otherset.sets.size(); ++i) {
      if (otherset.set_index[i] == added) {
        continue;
      }
      
    }
  }

  bool IsCovered() {
    return uncovered.empty();
  }
};

std::vector<int> GreedyAlg(Set remain) {
  if (remain.IsCovered()) {
    return {};
  }
  std::vector<int> ans;
  while (!remain.IsCovered()) {
    int min_ind = -1;
    double min_cost = cInfty;
    for (size_t i = 0; i < remain.sets.size(); ++i) {
      if (remain.sets[i].empty()) {
        continue;
      }
      double cost = static_cast<double>(remain.set_costs[i])
        / static_cast<double>(remain.sets[i].size());
      if (cost < min_cost) {
        min_ind = static_cast<int>(i);
        min_cost = cost;
      }
    }
    if (min_ind == -1) {
      throw std::runtime_error("Min ind is impossible!!!");
    }
    ans.push_back(min_ind);
    for (auto iter = remain.sets[min_ind].begin();
      iter != remain.sets[min_ind].end(); ++iter) {
      remain.uncovered.erase(*iter);
      for (size_t i = 0; i < remain.sets.size(); ++i) {
        if (i == min_ind) {
          continue;
        }
        remain.sets[i].erase(*iter);
      }
    }
    remain.sets[min_ind].clear();
  }
  return ans;
}

Set InputData(std::string path) {
  std::ifstream input_file(path);
  std::string line;
  int set_size;
  int subset_num;
  std::getline(input_file, line);
  std::vector<int> nm = StringToInt(line);
  std::vector<std::string> all_lines;
  while(std::getline(input_file, line)) {
    all_lines.push_back(line);
  }
  Set inp(nm[0], all_lines);
  return inp;
}

std::vector<int> SetCover(std::string path, std::ostringstream& out) {
  Set inp = InputData(path);
  std::vector<int> gredeur = GreedyAlg(inp);
  long long ans = 0;
  for (size_t i = 0; i < gredeur.size(); ++i) {
    ans += inp.set_costs[gredeur[i]];
  }
  out << ans << "\n";
  for (size_t i = 0; i < gredeur.size(); ++i) {
    out << gredeur[i] << " ";
  }
  out << std::endl;
  return {0};
}