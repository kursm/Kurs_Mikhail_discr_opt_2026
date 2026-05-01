#include <array>
#include <chrono>
#include <cmath>
#include <fstream>
#include <iomanip>
#include <iostream>
#include <sstream>
#include <string>
#include <vector>
#include "main.cpp"

std::array<std::string, 6> tests = {"vrp_16_3_1", "vrp_26_8_1", "vrp_51_5_1",
    "vrp_101_10_1", "vrp_200_16_1", "vrp_421_41_1"};
std::array<int, 6> ans_low = {387, 1019, 713, 1193, 3719, 2392};
std::array<int, 6> ans_high = {280, 630, 540, 830, 1400, 2000};
std::string path = "./data/";

using dob = long double;
const dob cEps = 1E-3;

struct Point {
  dob demand = 0;
  dob x = 0;
  dob y = 0;
};

dob Dist(const Point& a, const Point& b) {
  dob dx = a.x - b.x;
  dob dy = a.y - b.y;
  return std::sqrt(dx * dx + dy * dy);
}

bool Correct(std::string ans, int test) {
  std::ifstream input_file(path + tests[test]);
  int n;
  int v;
  dob c;
  input_file >> n >> v >> c;
  std::vector<Point> points(n + 1);
  points[0].demand = 0;
  points[0].x = 0;
  points[0].y = 0;
  for (int i = 1; i <= n; ++i) {
    input_file >> points[i].demand >> points[i].x >> points[i].y;
  }
  std::istringstream inn(ans);
  std::string line;
  dob sum;
  inn >> sum;
  std::vector<std::vector<int>> order;
  std::getline(inn, line);
  while (std::getline(inn, line)) {
    std::istringstream rs(line);
    std::vector<int> route;
    int x;
    while (rs >> x) {
      route.push_back(x);
    }
    order.push_back(std::move(route));
  }
  if (static_cast<int>(order.size()) != v) {
    return false;
  }
  std::vector<int> visits(n + 1, 0);
  dob ans_sum = 0;
  for (int i = 0; i < v; ++i) {
    const std::vector<int>& route = order[i];
    if (route.size() < 2) {
      return false;
    }
    if (route.front() != 0 || route.back() != 0) {
      return false;
    }
    dob cur_load = 0;
    for (size_t j = 0; j + 1 < route.size(); ++j) {
      int a = route[j];
      int b = route[j + 1];
      if (a < 0 || a > n || b < 0 || b > n) {
        return false;
      }
      ans_sum += Dist(points[a], points[b]);
    }
    for (size_t j = 0; j + 1 < route.size(); ++j) {
      int node = route[j];
      ++visits[node];
      cur_load += points[node].demand;
    }
    if (cur_load > c + cEps) {
      return false;
    }
  }
  if (visits[0] != v)  {
    return false;
  }
  for (int node = 1; node <= n; ++node) {
    if (visits[node] != 1) {
      return false;
    }
  }
  if (std::abs(ans_sum - sum) > cEps) {
    return false;
  }
  return true;
}

int main() {
  int sum = 0;
  for (int i = 0; i < 6; ++i) {
    auto start = std::chrono::steady_clock::now();
    std::ostringstream out;
    try {
      VRPSolver sol(path + tests[i], out);
    }
    catch (const std::exception& e) {
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
