#include <array>
#include <chrono>
#include <fstream>
#include <iomanip>
#include <iostream>
#include <set>
#include <sstream>
#include <string>
#include <vector>
#include "main.cpp"

std::array<std::string, 6> tests = {"sc_157_0", "sc_330_0", "sc_1000_11",
    "sc_5000_1", "sc_10000_5", "sc_10000_2"};
std::array<int, 6> ans_low = {130000, 29, 240, 70, 120, 280};
std::array<int, 6> ans_high = {94402, 24, 147, 31, 64, 167};
std::string path = "./Setcover/data/";

bool Correct(std::string ans, int test) {
  std::ifstream input_file(path + tests[test]);
  int n = 0;
  int m = 0;
  input_file >> n >> m;
  std::vector<long long> set_cost(m, 0);
  std::vector<std::set<int>> set_elements(m);
  for (int i = 0; i < m; ++i) {
    input_file >> set_cost[i];
    std::string line;
    std::getline(input_file, line);
    std::istringstream line_stream(line);
    int element = 0;
    while (line_stream >> element) {
      set_elements[i].insert(element);
    }
  }
  std::istringstream inp(ans);
  long long ans_sum = 0;
  if (!(inp >> ans_sum)) {
    return false;
  }
  std::vector<int> chosen_sets;
  int set_id = 0;
  while (inp >> set_id) {
    if (set_id < 0 || set_id >= m) {
      return false;
    }
    chosen_sets.push_back(set_id);
  }
  long long real_sum = 0;
  for (size_t i = 0; i < chosen_sets.size(); ++i) {
    real_sum += set_cost[chosen_sets[i]];
  }
  if (real_sum != ans_sum) {
    return false;
  }
  std::vector<int> cover_count(n, 0);
  for (size_t i = 0; i < chosen_sets.size(); ++i) {
    for (int element : set_elements[chosen_sets[i]]) {
      if (element < 0 || element >= n) {
        return false;
      }
      ++cover_count[element];
    }
  }
  for (int i = 0; i < n; ++i) {
    if (cover_count[i] == 0) {
      return false;
    }
  }
  return true;
}

int main() {
  int sum = 0;
  for (int i = 0; i < 6; ++i) {
    auto start = std::chrono::steady_clock::now();
    std::ostringstream out;
    try {
      SetCoverSolver(path + tests[i], out);
    }
    catch (const std::exception&) {
      std::cout << "Test " << i + 1 << ": no answer, runtime error;\n";
      continue;
    }
    std::string ans = out.str();
    std::cout << std::fixed << std::setprecision(3);
    if (Correct(ans, i)) {
      std::cout << "Test " << i + 1 << ": correct answer; "; 
    } else {
      std::cout << "Test " << i + 1 << ": incorrect answer!!;\n";
      continue;
    }
    auto end = std::chrono::steady_clock::now();
    auto duration = std::chrono::duration_cast<std::chrono::milliseconds>(end - start);
    std::cout << "Time taken: " << double(duration.count()) / 1000 << " seconds" << "\n";
    std::istringstream ans_stream(ans);
    long long ans_val = 0;
    ans_stream >> ans_val;
    if (ans_val <= ans_high[i]) {
      std::cout << "Answer is " << ans_val << ", 5 Points received!\n";
      sum += 5;
    } else {
      if (ans_val <= ans_low[i]) {
        std::cout << "Answer is " << ans_val << ", 3 Points received!\n";
        sum += 3;
      } else {
        std::cout << "Answer is " << ans_val << ", 0 Points received!\n";
      }
    }
  }
  std::cout << "Total sum of points is: " << sum << "\n";
}
