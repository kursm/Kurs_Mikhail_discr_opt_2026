#include <array>
#include <chrono>
#include <sstream>
#include <iostream>
#include <string>
#include "main.cpp"

std::array<std::string, 6> tests = {"tsp_51_1", "tsp_100_3", "tsp_200_2",
    "tsp_574_1", "tsp_1889_1", "tsp_33810_1"};
std::array<int, 6> ans_low = {482, 23433, 35985, 40000, 378069, 78478868};
std::array<int, 6> ans_high = {430, 20800, 30000, 37600, 323000, 67700000};
std::string path = "./data/";

using dob = long double;

bool Correct(std::string ans, int test) {
  std::ifstream input_file(path + tests[test]);
  int n;
  input_file >> n;
  std::vector<std::pair<dob, dob>> points(n);
  for (int i = 0; i < n; ++i) {
    input_file >> points[i].first >> points[i].second;
  }

  std::string line;
  std::istringstream inn(ans);
  dob sum;
  inn >> sum;
  std::vector<int> order;
  int ver;
  while (inn >> ver) {
    order.push_back(ver);
  }

  if (order.size() != n) {
    return false;
  }

  std::vector<bool> is_used(n, false);
  for (int i = 0; i < n; ++i) {
    if (is_used[order[i]]) {
      return false;
    }
    is_used[order[i]] = true;
  }
  for (int i = 0; i < n; ++i) {
    if (!is_used[i]) {
      return false;
    }
  }

  dob ans_sum = 0;
  for (int i = 0; i < n - 1; ++i) {
    dob x_square = points[order[i]].first - points[order[i + 1]].first;
    dob y_square = points[order[i]].second - points[order[i + 1]].second;
    ans_sum += std::sqrt(x_square * x_square + y_square * y_square);
  }
  dob x_square = points[order[0]].first - points[order[n - 1]].first;
  dob y_square = points[order[0]].second - points[order[n - 1]].second;
  ans_sum += std::sqrt(x_square * x_square + y_square * y_square);

  if (std::abs(ans_sum - sum) > 0.1) {
    return false;
  }
  return true;
}

int main() {
  int sum = 0;
  for (int i = 0; i < 6; ++i) {
    auto start = std::chrono::steady_clock::now();
    std::ostringstream out;
    TSPSolver sol(path + tests[i], out);
    std::string ans = out.str();
    std::cout << std::fixed << std::setprecision(2);
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
    dob ans_val;
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