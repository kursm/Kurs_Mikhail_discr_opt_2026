#include <algorithm>
#include <cmath>
#include <iostream>
#include <fstream>
#include <set>
#include <sstream>
#include <stdexcept>
#include <string>
#include <vector>

//std::string path = "Setcover/data/sc_10000_2";
const int cInfty = 10000000;
const long long cMaxTime = 2E10;
long long max_steps;
int depth;

bool Comparator(std::pair<double, int> first, std::pair<double, int> second) {
  return (first.first < second.first) ||
         ((first.first == second.first) && (first.second < second.second));
}

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
  int num_of_el;

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
    num_of_el = n;
    num_of_sets = sets.size();
  }

  Set (Set& otherset, int pos) {
    uncovered = otherset.uncovered;
    set_costs = otherset.set_costs;
    if (pos >= otherset.sets.size()) {
      std::cout << "BUG!" << std::endl;
    }
    for (auto iter = otherset.sets[pos].begin();
         iter != otherset.sets[pos].end(); ++iter) {
      uncovered.erase(*iter);
    }
    num_of_el = uncovered.size();
    for (size_t i = 0; i < otherset.sets.size(); ++i) {
      if (i == pos) {
        continue;
      }
      sets.push_back(otherset.sets[i]);
      set_index.push_back(otherset.set_index[i]);
      for (auto iter = otherset.sets[pos].begin();
           iter != otherset.sets[pos].end(); ++iter) {
        sets.back().erase(*iter);
      }
      if (sets.back().empty()) {
        sets.pop_back();
        set_index.pop_back();
      }
    }
    num_of_sets = sets.size();
  }

  bool IsCovered() {
    return uncovered.empty();
  }

  bool IsUncoverable() {
    std::set<int> uncovered_copy = uncovered;
    for (size_t i = 0; i < sets.size(); ++i) {
      for (auto iter = sets[i].begin(); iter != sets[i].end(); ++iter) {
        uncovered_copy.erase(*iter);
      }
      if (uncovered_copy.empty()) {
        return false;
      }
    }
    return true;
  }

  void DataSort() {
    std::vector<std::pair<double, int>> elcost;
    elcost.reserve(num_of_sets);
    for (size_t i = 0; i < sets.size(); ++i) {
      double cost = cInfty;
      if (!sets[i].empty()) {
        cost = static_cast<double>(set_costs[set_index[i]]) /
               static_cast<double>(sets[i].size());
      }
      elcost.push_back(std::pair<double, int>(cost, i));
    }
    std::sort(elcost.begin(), elcost.end(), Comparator);
    std::vector<std::set<int>> sets_sort;
    std::vector<int> set_costs_sort;
    std::vector<int> set_index_sort;
    sets_sort.reserve(sets.size());
    set_index_sort.reserve(set_index.size());
    for (size_t i = 0; i < elcost.size(); ++i) {
      if (elcost[i].first != cInfty) {
        sets_sort.push_back(sets[elcost[i].second]);
        set_index_sort.push_back(set_index[elcost[i].second]);
      }
    }
    std::swap(sets_sort, sets);
    std::swap(set_index_sort, set_index);
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
    ans.push_back(remain.set_index[min_ind]);
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

int GetGreadyAns(Set& inp, std::vector<int> gredeur) {
  int ans = 0;
  for (size_t i = 0; i < gredeur.size(); ++i) {
    ans += inp.set_costs[gredeur[i]];
  }
  return ans;
}

std::vector<int> best_known = {};
long long best_known_sum = cInfty;

std::vector<int> PilotMethod(Set remain, int c_sum = 0, int dep = 0,
                             std::vector<int> c_ans = {}) {
  static int counter = 0;
  if (dep == 0) {
    counter = 0;
    best_known = {};
    best_known_sum = cInfty;
  }
  ++counter;
  /**if (counter % 10000 == 0) {
    std::cout << counter << " " << max_steps << std::endl;
  }*/
  std::vector<int> some_ans = GreedyAlg(remain);
  long long some_ans_value = GetGreadyAns(remain, some_ans);
  if(some_ans_value + c_sum < best_known_sum) {
    best_known_sum = some_ans_value + c_sum;
    best_known = c_ans;
    for (size_t i = 0; i < some_ans.size(); ++i) {
      best_known.push_back(some_ans[i]);
    }
  }
  remain.DataSort();
  if ((counter > max_steps) || (dep > depth)) {
    return GreedyAlg(remain);
  }
  double h = 0.1;
  for (int i = 1; i <= remain.num_of_el; ++i) {
    h += static_cast<double>(1) / static_cast<double>(i);
  }
  if (static_cast<double>(some_ans_value) / h > double(best_known_sum)) {
    return GreedyAlg(remain);
  }
  if (remain.IsCovered()) {
    if (c_sum < best_known_sum) {
      c_sum = best_known_sum;
      best_known = c_ans;
    }
    return {};
  }
  Set taken(remain, remain.sets.size() - 1);
  auto c_ans_taken = c_ans;
  c_ans_taken.push_back(remain.set_index[remain.sets.size() - 1]);
  int c_sum_taken = c_sum +
      remain.set_costs[remain.set_index[remain.sets.size() - 1]];
  some_ans = PilotMethod(taken, c_sum_taken, dep + 1, c_ans_taken);
  some_ans_value = GetGreadyAns(taken, some_ans) + c_sum_taken;
  if (some_ans_value < best_known_sum) {
    best_known_sum = some_ans_value;
    best_known = some_ans;
    for (size_t i = 0; i < c_ans_taken.size(); ++i) {
      best_known.push_back(c_ans_taken[i]);
    }
  }
  remain.set_index.pop_back();
  remain.sets.pop_back();
  --remain.num_of_sets;
  if (remain.IsUncoverable()) {
    return best_known;
  }
  some_ans = PilotMethod(remain, c_sum_taken, dep + 1, c_ans);
  some_ans_value = GetGreadyAns(remain, some_ans) + c_sum;
  if (some_ans_value < best_known_sum) {
    best_known_sum = some_ans_value;
    best_known = some_ans;
    for (size_t i = 0; i < c_ans.size(); ++i) {
      best_known.push_back(c_ans[i]);
    }
  }
  return best_known;
}

std::vector<int> SetCover(std::string path, std::ostringstream& out) {
  Set inp = InputData(path);
  long long one_step = 1;
  one_step *= inp.num_of_el;
  one_step *= inp.num_of_sets;
  one_step *= (std::log2(inp.num_of_el) + 1);
  max_steps = cMaxTime / one_step;
  depth = std::log2(max_steps) + 10;
  std::vector<int> pilot = PilotMethod(inp);
  //std::vector<int> gredeur = GreedyAlg(inp);
  std::vector<int>& gredeur = pilot;
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