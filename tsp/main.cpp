#include <algorithm>
#include <cassert>
#include <cmath>
#include <iomanip>
#include <iostream>
#include <fstream>
#include <random>
#include <set>
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
  std::vector<std::set<int>> is_neib;
  std::vector<std::set<SPair>> sr_neib;
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

  void AddNeibShip(int u, int v) {
    if (is_neib[u].count(v) == 1) {
      return;
    }
    is_neib[u].insert(v);
    sr_neib[u].insert(SPair(Dist(u, v), v));
  }

  void GetNeighbours(int num) {
    is_neib.resize(num_of_points);
    sr_neib.resize(num_of_points);
    std::vector<SPair> x_sort;
    std::vector<SPair> y_sort;
    x_sort.reserve(num_of_points);
    y_sort.reserve(num_of_points);
    for (int i = 0; i < num_of_points; ++i) {
      x_sort.push_back(SPair(points[i].first, i));
      y_sort.push_back(SPair(points[i].second, i));
    }
    std::sort(x_sort.begin(), x_sort.end(), Comp1);
    std::sort(y_sort.begin(), y_sort.end(), Comp1);
    for (int i = 0; i < num_of_points; ++i) {
      for (int j = 0; j < std::min(num, num_of_points - i); ++j) {
        AddNeibShip(x_sort[i].second, x_sort[i + j].second);
        AddNeibShip(x_sort[i + j].second, x_sort[i].second);
        AddNeibShip(y_sort[i].second, y_sort[i + j].second);
        AddNeibShip(y_sort[i + j].second, y_sort[i].second);
      }
    }
  }

  Ans ClosestEur2(int first) {
    std::vector<bool> is_used(num_of_points, false);
    Ans ans;
    ans.first.reserve(num_of_points);
    ans.first.push_back(first);
    is_used[first] = true;
    int f_start = 0;
    for (int i = 0; i < num_of_points - 1; ++i) {
      bool is_done = false;
      for (const auto& neib: sr_neib[ans.first[i]]) {
        if (!is_used[neib.second]) {
          is_used[neib.second] = true;
          ans.first.push_back(neib.second);
          is_done = true;
          break;
        }
      }
      if (!is_done) {
        for (int j = f_start; j < num_of_points; ++j) {
          if (is_used[j]) {
            ++f_start;
            continue;
          }
          is_used[j] = true;
          AddNeibShip(ans.first[i], j);
          AddNeibShip(j, ans.first[i]);
          ans.first.push_back(j);
          break;
        }
      }
    }
    ans.second = FindDist(ans.first);
    return ans;
  }

  db TwoOptBen(const Ans& ans, int first, int second) {
    int u1 = ans.first[first];
    int v1 = ans.first[(first + 1) % num_of_points];
    int u2 = ans.first[second];
    int v2 = ans.first[(second + 1) % num_of_points];
    db have = Dist(u1, v1) + Dist(u2, v2);
    db will_have = Dist(u1, u2) + Dist(v1, v2);
    return will_have - have;
  }

  void TwoOpt(Ans& ans, int first, int second) {
    ans.second += TwoOptBen(ans, first, second);
    if (first > second) {
      std::swap(first, second);
    }
    std::reverse(ans.first.begin() + first + 1, ans.first.begin() + second + 1);
  }

  Ans TwoOptMaxIter(Ans ans) {
    for (int iter = 0; iter < two_opt_iters; ++iter) {
      bool improved = false;
      for (int i = 0; i < num_of_points; ++i) {
        for (int j = i + 2; j < num_of_points; ++j) {
          if (TwoOptBen(ans, i, j) < 0) {
            TwoOpt(ans, i, j);
            improved = true;
            break;
          }
        }
        if (improved) {
          break;
        }
      }
      if (!improved) {
        std::cout << "num_of_iters:" << iter << "\n";
        break;
      }
    }
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
  int cNumOfneigh = 250;
  int beg_iters = 500;
  int two_opt_iters = 500;
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
    } else {
      GetNeighbours(cNumOfneigh);
      two_opt_iters = 200;
      eur = ClosestEur2(0);
      best_known = eur;
      std::random_device rd;
      std::mt19937 gen(rd());
      std::uniform_int_distribution<int> dist(0, num_of_points - 1); 
      for (int i = 1; i < beg_iters; ++i) {
        eur = ClosestEur2(dist(gen));
        MakeBetter(eur);
      }
    }
    //eur = TwoOptMaxIter(best_known);
    //MakeBetter(eur);
    OutAns(out);
  }
};

/*int main() {
  std::ostringstream out;
  TSPSolver solve("data/tsp_51_1", out);
  std::cout << out.str();
}*/