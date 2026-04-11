#include <algorithm>
#include <cassert>
#include <cmath>
#include <iomanip>
#include <iostream>
#include <fstream>
#include <sstream>
#include <stdexcept>
#include <string>
#include <vector>

struct TSPSolver{
 private:
  using db = long double;
  using Pair = std::pair<db, db>;
  using SPair = std::pair<db, int>;
  using Ans = std::pair<std::vector<int>, db>;
  std::vector<Pair> points;
  std::vector<std::vector<int>> sort_order;
  int num_of_points;
  bool sort_order_is_set = false;

  void InputData(std::string& path) {
    std::ifstream input_file(path);
    input_file >> num_of_points;
    points.resize(num_of_points);
    for(int i = 0; i < num_of_points; ++i) {
      input_file >> points[i].first >> points[i].second;
    }
  }

  db Dist(int num1, int num2) {
    db x_sq = points[num1].first - points[num2].first;
    db y_sq = points[num1].second - points[num2].second;
    return std::sqrt(x_sq * x_sq + y_sq * y_sq);
  }

  static bool Comp1(SPair first, SPair second) {
    return first.first < second.first;
  }

  void MakeSortOrder() {
    for (int i = 0; i < num_of_points; ++i) {
      std::vector<SPair> dist;
      dist.reserve(num_of_points);
      for (int j = 0; j < num_of_points; ++j) {
        dist.push_back(SPair(Dist(i, j), j));
      }
      std::sort(dist.begin(), dist.end(), Comp1);
      sort_order.push_back(std::vector<int>());
      for (int j = 0; j < num_of_points; ++j) {
        sort_order.back().push_back(dist[j].second);
      }
    }
    sort_order_is_set = true;
  }

  db FindDist(std::vector<int>& perm) {
    db ans = 0;
    for (size_t i = 0; i < perm.size() - 1; ++i) {
      ans += Dist(perm[i], perm[i + 1]);
    }
    ans += Dist(perm[0], perm.back());
    return ans;
  }

  Ans ClosestEur(int first) {
    std::vector<bool> is_used(num_of_points, false);
    Ans ans;
    assert(sort_order_is_set);
    ans.first.reserve(num_of_points);
    ans.first.push_back(first);
    is_used[first] = true;
    for (int i = 0; i < num_of_points - 1; ++i) {
      for (int j = 0; j < num_of_points; ++j) {
        if (!is_used[sort_order[ans.first[i]][j]]) {
          is_used[sort_order[ans.first[i]][j]] = true;
          ans.first.push_back(sort_order[ans.first[i]][j]);
          break;
        }
      }
    }
    ans.second = FindDist(ans.first);
    return ans;
  }

  void OutAns(std::ostringstream& out) {
    out << std::fixed << std::setprecision(5) << best_known.second << "\n";
    for (size_t i = 0; i < best_known.first.size(); ++i) {
      out << best_known.first[i] << " ";
    }
    out << "\n";
  }

  void MakeBetter(Ans& other) {
    if (other.second < best_known.second) {
      std::swap(other, best_known);
    }
  }

 public:

  int cMaxForSort = 1915; // Max time is 2 seconds, since x^2 log_2(x)
  Ans best_known;
 
  TSPSolver(std::string path, std::ostringstream& out) {
    InputData(path);
    Ans eur;
    if (num_of_points < cMaxForSort) {
      MakeSortOrder();
      eur = ClosestEur(0);
      best_known = eur;
      for (int i = 1; i < num_of_points - 1; ++i) {
        eur = ClosestEur(i);
        MakeBetter(eur);
      }
    }
    OutAns(out);
  }
};

/*int main() {
  std::ostringstream out;
  TSPSolver solve("data/tsp_51_1", out);
  std::cout << out.str();
}*/