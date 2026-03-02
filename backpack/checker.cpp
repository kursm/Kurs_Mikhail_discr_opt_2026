#include <array>
#include <sstream>
#include <iostream>
#include <string>
#include "main.cpp"

std::array<std::string, 6> tests = {"ks_30_0", "ks_50_0", "ks_200_0",
    "ks_400_0", "ks_1000_0", "ks_10000_0"};
std::array<int, 6> ans_low = {92000, 141956, 100062, 3966813, 109869, 1099870};
std::array<int, 6> ans_high = {99798, 142156, 100236, 3967028, 109899, 1099881};
std::string path = "./data/";

bool Correct(std::string ans, int test) {
  std::ifstream input_file(path + tests[test]);
  int num_of_obj;
  int max_wei;
  input_file >> num_of_obj >> max_wei;
  std::vector<int> obj_cost(num_of_obj);
  std::vector<int> obj_wei(num_of_obj);
  for (int i = 0; i < num_of_obj; ++i) {
    input_file >> obj_cost[i] >> obj_wei[i];
  }
  std::string line;
  std::istringstream inn(ans);
  std::getline(inn, line);
  long long prop_cost = std::stoi(line);
  long long sum_cost = 0;
  long long sum_wei = 0;
  std::getline(inn, line);
  std::istringstream inn_ind(line);
  std::vector<int> ind;
  int ind_inp;
  while (inn_ind >> ind_inp) {
    ind.push_back(ind_inp);
  }
  for (int i = 0; i < ind.size(); ++i) {
    sum_cost += obj_cost[ind[i]];
    sum_wei += obj_wei[ind[i]];
  }
  return (sum_cost == prop_cost) && (sum_wei <= max_wei);
}

bool IsDp(std::string ans) {
  std::string line;
  std::istringstream inn(ans);
  std::getline(inn, line);
  std::getline(inn, line);
  if (std::getline(inn, line)) {
    return (line == "Full DP");
  }
  return false;
}

int main() {
  int sum = 0;
  for (int i = 0; i < 6; ++i) {
    std::ostringstream out;
    BackPack(path + tests[i], out);
    std::string ans = out.str();
    if (Correct(ans, i)) {
      std::cout << "Test " << i + 1 << ": correct answer; "; 
    } else {
      std::cout << "Test " << i + 1 << ": incorrect answer!!;\n";
      continue;
    }
    std::istringstream inn(ans);
    long long ans_val;
    inn >> ans_val;
    if (ans_val >= ans_high[i]) {
      if (IsDp(ans)) {
        std::cout << "Answer is " << ans_val << ", it is accurate, 5 Points received!\n";
        sum += 5;
      } else {
        std::cout << "Answer is " << ans_val << ", 5 Points received!\n";
        sum += 5;
      }
    } else {
      if (ans_val >= ans_low[i]) {
        std::cout << "Answer is " << ans_val << ", 3 Points received!\n";
        sum += 3;
      } else {
        std::cout << "Answer is " << ans_val << ", 0 Points received!\n";
      }
    }
  }
  std::cout << "Total sum of points is: " << sum << "\n";
}