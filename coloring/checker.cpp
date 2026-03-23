#include <array>
#include <chrono>
#include <sstream>
#include <iostream>
#include <string>
#include "main.cpp"

std::array<std::string, 6> tests = {"gc_50_3", "gc_70_7", "gc_100_5",
    "gc_250_9", "gc_500_1", "gc_1000_5"};
std::array<int, 6> ans_low = {8, 20, 21, 95, 18, 124};
std::array<int, 6> ans_high = {6, 17, 16, 78, 16, 100};
std::string path = "./data/";

bool Correct(std::string ans, int test) {
  std::ifstream input_file(path + tests[test]);
  int ver;
  int edg;
  input_file >> ver >> edg;

  std::string line;
  std::istringstream inn(ans);
  int num_of_col;
  inn >> num_of_col;
  std::vector<int> colors;
  for (int i = 0; i < ver; ++i) {
    int col;
    if (inn >> col) {
      colors.push_back(col);
    } else {
      return false;
    }
    if ((col < 1) || (col > num_of_col)) {
      return false;
    }
  }
  int is_all;
  if (inn >> is_all) {
    return false;
  }
  for (int i = 0; i < edg; ++i) {
    int u;
    int v;
    input_file >> u >> v;
    if (colors[u] == colors[v]) {
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
    ColoringSolver sol(path + tests[i], out);
    std::string ans = out.str();
    if (Correct(ans, i)) {
      std::cout << "Test " << i + 1 << ": correct answer; "; 
    } else {
      std::cout << "Test " << i + 1 << ": incorrect answer!!;\n";
      continue;
    }
    auto end = std::chrono::steady_clock::now();
    auto duration = std::chrono::duration_cast<std::chrono::milliseconds>(end - start);
    std::cout << "Time taken: " << double(duration.count()) / 1000 << " seconds" << "\n";
    std::istringstream inn(ans);
    long long ans_val;
    inn >> ans_val;
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