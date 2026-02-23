#include <array>
#include <sstream>
#include <iostream>
#include <string>
#include "main.cpp"

std::array<std::string, 6> tests = {"sc_157_0", "sc_330_0", "sc_1000_11",
    "sc_5000_1", "sc_10000_5", "sc_10000_2"};
std::array<int, 6> ans_low = {130000, 29, 240, 70, 120, 280};
std::array<int, 6> ans_high = {94402, 24, 147, 31, 64, 167};
std::string path = "./setcover/Setcover/data/";

bool Correct(std::string ans, int test) {
  std::ifstream input_file(path + tests[test]);
  std::string line;
  int set_size;
  int subset_num;
  std::getline(input_file, line);
  std::vector<int> nm = StringToInt(line);
  std::vector<std::vector<int>> all_lines;
  while(std::getline(input_file, line)) {
    all_lines.push_back(StringToInt(line)); // StringToInt is defined in main
  }
  std::vector<int> ans_vec = StringToInt(ans);
  int ans_sum = ans_vec[0];
  long long ans_real = 0;
  for (size_t i = 1; i < ans_vec.size(); ++i) {
    ans_real += all_lines[ans_vec[i]][0];
  }
  if (ans_sum != ans_real) {
    return false;
  }

  std::vector<bool> is_covered(nm[0], false);
  for (size_t i = 1; i < ans_vec.size(); ++i) {
    for (size_t j = 1; j < all_lines[ans_vec[i]].size(); ++j) {
      is_covered[all_lines[ans_vec[i]][j]] = true;
    }
  }
  for (size_t i = 0; i < is_covered.size(); ++i) {
    if (!is_covered[i]) {
      return false;
    }
  }
  return true;
}

int main() {
  int sum = 0;
  for (int i = 0; i < 6; ++i) {
    std::ostringstream out;
    SetCover(path + tests[i], out);
    std::string ans = out.str();
    if (Correct(ans, i)) {
      std::cout << "Test " << i + 1 << ": correct answer; "; 
    }
    else {
      std::cout << "Test " << i + 1 << ": incorrect answer!!;\n";
      continue;
    }
    std::vector<int> ans_vec = StringToInt(ans);
    if (ans_vec[0] <= ans_high[i]) {
      std::cout << "Answer is " << ans_vec[0] << ", 5 Points received!\n";
      sum += 5;
    }
    else {
      if (ans_vec[0] <= ans_low[i]) {
        std::cout << "Answer is " << ans_vec[0] << ", 3 Points received!\n";
        sum += 3;
      }
      else {
        std::cout << "Answer is " << ans_vec[0] << ", 0 Points received!\n";
      }
    }
  }
  std::cout << "Total sum of points is: " << sum << "\n";
}