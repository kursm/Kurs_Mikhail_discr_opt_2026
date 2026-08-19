#include <array>
#include <chrono>
#include <sstream>
#include <iostream>
#include <string>
#include "main.cpp"

std::array<std::string, 6> tests = {"fl_25_2", "fl_100_1", "fl_200_7",
    "fl_500_7", "fl_1000_2", "fl_2000_2"};
std::array<int, 6> ans_low = {4000000, 26000000, 5000000, 30000000, 10000000, 10000000};
std::array<int, 6> ans_high = {3269822, 22724634, 4711295, 27006099, 8879294, 7453531};
std::string path = "./data/";

using dob = long double;

dob Dist(dob x_f, dob y_f, dob x_s, dob y_s) {
  dob x_sq = x_f - x_s;
  dob y_sq = y_f - y_s;
  return std::sqrt(x_sq * x_sq + y_sq * y_sq);
}

bool Correct(std::string ans, int test) {
  std::ifstream input_file(path + tests[test]);
  int shops;
  int people;
  input_file >> shops >> people;
  std::vector<long double> open, cap, shop_x, shop_y;
  std::vector<long double> demand, guy_x, guy_y;
  open.resize(shops);
  cap.resize(shops);
  shop_x.resize(shops);
  shop_y.resize(shops);
  demand.resize(people);
  guy_x.resize(people);
  guy_y.resize(people);
  for (int i = 0; i < shops; ++i) {
    input_file >> open[i] >> cap[i] >> shop_x[i] >> shop_y[i];
  }
  for (int i = 0; i < people; ++i) {
    input_file >> demand[i] >> guy_x[i] >> guy_y[i];
  }
  std::set<int> is_used;
  std::vector<long double> taken(shops, 0);

  std::string line;
  std::istringstream inn(ans);
  dob sum;
  inn >> sum;
  std::vector<int> order;
  int ver;
  int iter = 0;
  while (inn >> ver) {
    order.push_back(ver);
    is_used.insert(ver);
    taken[ver] += demand[iter];
    ++iter;
  }

  if (order.size() != people) {
    return false;
  }

  for (int i = 0; i < shops; ++i) {
    if (taken[i] > cap[i]) {
      return false;
    }
  }

  long double ans_sum = 0;
  for (int i = 0; i < people; ++i) {
    ans_sum += Dist(guy_x[i], guy_y[i], shop_x[order[i]], shop_y[order[i]]);
  }

  for (auto i: is_used) {
    ans_sum += open[i];
  }

  if (std::abs(ans_sum - sum) > 0.02) {
    return false;
  }
  return true;
}

int main() {
  int sum = 0;
  std::ofstream output_file("output.txt");
  for (int i = 0; i < 6; ++i) {
    auto start = std::chrono::steady_clock::now();
    std::ostringstream out;
    FacilitySolver sol(path + tests[i], out);
    std::string ans = out.str();
    output_file << "Test " << tests[i] << ":\n" << ans << std::endl;
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
