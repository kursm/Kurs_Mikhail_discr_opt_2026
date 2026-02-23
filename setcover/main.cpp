#include <iostream>
#include <fstream>
#include <set>
#include <string>
#include <vector>

std::string path = "Setcover/data/sc_9_0";
const int cInfty = 10000000;

std::vector<int> StringToInt(std::string str) {
  std::string int_str;
  std::vector<int> ans;
  for (size_t i = 0; i < str.size(); ++i) {
    if (str[i] == ' ') {
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

  void GreedyEur(std::vector<int>& ans) {
    if (IsCovered()) {
      return;
    }
    int min_ind = -1;
    double min_cost = cInfty;
    for (size_t i = 0; i < sets.size(); ++i) {
      if (sets[i].empty()) {
        continue;
      }
      double cost = static_cast<double>(set_costs[i])
        / static_cast<double>(sets[i].size());
      if (cost < min_cost) {
        min_ind = static_cast<int>(i);
        min_cost = cost;
      }
    }
    ans.push_back(min_ind);
    Set(*this, min_ind).GreedyEur(ans);
  }

  bool IsCovered() {
    return uncovered.empty();
  }
};

std::vector<int> GreedyAlg(Set remain) {
  
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

std::vector<int> SetCover(std::string path) {
  Set inp = InputData(path);
  std::vector<int> gredeur;
  inp.GreedyEur(gredeur);
  for (size_t i = 0; i < gredeur.size(); ++i) {
    std::cout << gredeur[i] << " ";
  }
  std::cout << std::endl;
  return {0};
}

int main() {
  SetCover(path);
}