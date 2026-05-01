#include <algorithm>
#include <cassert>
#include <cmath>
#include <chrono>
#include <iomanip>
#include <iostream>
#include <fstream>
#include <random>
#include <set>
#include <sstream>
#include <stdexcept>
#include <string>
#include <vector>

struct VRPSolver {
 private:

  struct Shopper;
  using db = long double;
  static inline const db cInfty = 1E8;
  static inline const int cIntInfty = 1E6;
  db cEps = 0.01;
  int n = 0;
  int v = 0;
  int cGredTimes = 5000;
  int cMaxGredTime = 300;
  db c = 0;
  db cur_ans_val;
  db best_ans_val = cInfty;
  std::vector<db> cur_demand;
  std::vector<int> begins;
  std::vector<int> ends;
  std::vector<std::vector<int>> best_ans;
  std::vector<std::vector<int>> sort_dist;
  std::vector<Shopper> shoppers;

  struct Shopper {
    db x;
    db y;
    db demand;
    int next = -1;
    int prev = -1;
    int car = -1;
    bool is_warehouse = false;
    bool is_beg = false;
    bool is_end = false;

    Shopper() = default;

    Shopper(db x, db y, db demand, bool is_warehouse)
      : x(x)
      , y(y)
      , demand(demand)
      , is_warehouse(is_warehouse)
    {}
  };

  static db Dist(const Shopper& first, const Shopper& second) {
    db x_sq = first.x - second.x;
    db y_sq = first.y - second.y;
    return std::sqrt(x_sq * x_sq + y_sq * y_sq);
  }

  void InputData(std::string& path) {
    std::ifstream input_file(path);
    input_file >> n >> v >> c;
    shoppers.clear();
    shoppers.reserve(n + 1);
    shoppers.push_back(Shopper(0, 0, 0, true));
    for (int i = 0; i < n; ++i) {
      db demand;
      db x;
      db y;
      input_file >> demand >> x >> y;
      shoppers.push_back(Shopper(x, y, demand, false));
    }
  }

  void OutputData(std::ostringstream& out) {
    if (best_ans_val == cInfty) {
      throw std::runtime_error("No answer found!");
    }
    out << std::fixed << std::setprecision(5);
    out << best_ans_val << "\n";
    for (int i = 0; i < static_cast<int>(best_ans.size()); ++i) {
      for (int j = 0; j < static_cast<int>(best_ans[i].size()); ++j) {
        out << best_ans[i][j] << " ";
      }
      out << "\n";
    }
  }

  void FindAns() {
    cur_ans_val = 0;
    for (int i = 0; i < v; ++i) {
      if (begins[i] == 0) {
        continue;
      }
      int cur = begins[i];
      int prev = 0;
      while (true) {
        if (cur < 0 || cur >= static_cast<int>(shoppers.size())) {
          throw std::runtime_error("route vertex is out of range");
        }
        cur_ans_val += Dist(shoppers[prev], shoppers[cur]);
        if (cur == 0) {
          break;
        }
        prev = cur;
        cur = shoppers[cur].next;
      }
    }
  }

  void SetBetter() {
    if (best_ans_val < cur_ans_val) {
      return;
    }
    best_ans_val = cur_ans_val;
    best_ans.clear();
    best_ans.reserve(v);
    for (int i = 0; i < v; ++i) {
      std::vector<int> route;
      route.push_back(0);
      if (begins[i] != 0) {
        int cur = begins[i];
        while (true) {
          if (cur < 0 || cur >= static_cast<int>(shoppers.size())) {
            throw std::runtime_error("route vertex is out of range");
          }
          route.push_back(cur);
          if (cur == 0) {
            break;
          }
          cur = shoppers[cur].next;
        }
      } else {
        route.push_back(0);
      }
      best_ans.push_back(route);
    }
  }

  using SPair1 = std::pair<int, db>;

  static bool Comp1(SPair1 ft, SPair1 sc) {
    return ft.second < sc.second;
  }

  void FindSortDist() {
    sort_dist.clear();
    sort_dist.reserve(shoppers.size());
    for (int i = 0; i < static_cast<int>(shoppers.size()); ++i) {
      std::vector<SPair1> for_sort;
      for_sort.reserve(shoppers.size());
      for (int j = 0; j < static_cast<int>(shoppers.size()); ++j) {
        for_sort.push_back({j, Dist(shoppers[i], shoppers[j])});
      }
      std::sort(for_sort.begin(), for_sort.end(), Comp1);
      sort_dist.push_back({});
      sort_dist.back().reserve(shoppers.size());
      for (int j = 0; j < static_cast<int>(shoppers.size()); ++j) {
        sort_dist.back().push_back(for_sort[j].first);
      }
    }
  }

  void ClearShoppers() {
    for (int i = 0; i < static_cast<int>(shoppers.size()); ++i) {
      shoppers[i].next = -1;
      shoppers[i].prev = -1;
      shoppers[i].car = -1;
    }
    cur_demand.assign(v, 0);
  }

  void InsertShopperBetween(int who, int car, int from, int to) {
    shoppers[who].car = car;
    shoppers[who].prev = from;
    shoppers[who].next = to;
    shoppers[who].is_beg = (from == 0);
    shoppers[who].is_end = (to == 0);
    if (from == 0) {
      begins[car] = who;
    } else {
      shoppers[from].next = who;
      shoppers[from].is_end = false;
    }
    if (to == 0) {
      ends[car] = who;
    } else {
      shoppers[to].prev = who;
      shoppers[to].is_beg = false;
    }
    cur_demand[car] += shoppers[who].demand;
  }

  bool IsBetter(const Shopper& who, const Shopper& f_f, const Shopper& f_s,
                const Shopper& s_f, const Shopper& s_s) {
    db first = Dist(f_f, who) + Dist(who, f_s) - Dist(f_f, f_s);
    db second = Dist(s_f, who) + Dist(who, s_s) - Dist(s_f, s_s);
    return first >= second;
  }

  void BestNewPlace(int& best_car, int& best_from, int& best_to, int who) {
    for (int car = 0; car < v; ++car) {
      if (cur_demand[car] + shoppers[who].demand > c) {
        continue;
      }
      if (begins[car] == 0) {
        if (best_car == -1 ||
            IsBetter(shoppers[who], shoppers[best_from], shoppers[best_to],
                     shoppers[0], shoppers[0])) {
          best_car = car;
          best_from = 0;
          best_to = 0;
        }
        continue;
      }
      int from = 0;
      int to = begins[car];
      while (true) {
        if (best_car == -1 ||
            IsBetter(shoppers[who], shoppers[best_from], shoppers[best_to],
                     shoppers[from], shoppers[to])) {
          best_car = car;
          best_from = from;
          best_to = to;
        }
        if (to == 0) {
          break;
        }
        from = to;
        to = shoppers[to].next;
      }
    }
  }

  void OneGreedyEur(const std::vector<int>& perm) {
    ClearShoppers();
    begins.assign(v, 0);
    ends.assign(v, 0);
    for (int i = 0; i < static_cast<int>(shoppers.size()); ++i) {
      shoppers[i].is_beg = false;
      shoppers[i].is_end = false;
    }
    for (int it = 0; it < n; ++it) {
      int who = perm[it];
      if (who <= 0 || who >= static_cast<int>(shoppers.size())) {
        throw std::runtime_error("Wrong shopper index in perm");
      }
      int best_car = -1;
      int best_from = -1;
      int best_to = -1;
      BestNewPlace(best_car, best_from, best_to, who);
      if (best_car == -1) {
        throw std::runtime_error("Can't add anywhere");
      }
      InsertShopperBetween(who, best_car, best_from, best_to);
    }
  }

  int Resolve(const std::vector<int>& perm, int times = cIntInfty) {
    int improved_times = 0;
    while (true) {
      bool improved = false;
      for (int it = 0; it < n; ++it) {
        int who = perm[it];
        int old_car = shoppers[who].car;
        int old_prev = shoppers[who].prev;
        int old_next = shoppers[who].next;
        db rem_delta = Dist(shoppers[old_prev], shoppers[old_next]) -
                       Dist(shoppers[old_prev], shoppers[who]) -
                       Dist(shoppers[who], shoppers[old_next]);
        cur_demand[old_car] -= shoppers[who].demand;
        if (old_prev == 0) {
          begins[old_car] = old_next;
          if (old_next != 0) {
            shoppers[old_next].is_beg = true;
          }
        } else {
          shoppers[old_prev].next = old_next;
        }
        if (old_next == 0) {
          ends[old_car] = old_prev;
          if (old_prev != 0) {
            shoppers[old_prev].is_end = true;
          }
        } else {
          shoppers[old_next].prev = old_prev;
        }
        shoppers[who].car = -1;
        shoppers[who].prev = -1;
        shoppers[who].next = -1;
        shoppers[who].is_beg = false;
        shoppers[who].is_end = false;
        int best_car = -1;
        int best_from = -1;
        int best_to = -1;
        BestNewPlace(best_car, best_from, best_to, who);
        if (best_car == -1) {
          InsertShopperBetween(who, old_car, old_prev, old_next);
          continue;
        }
        db add_delta = Dist(shoppers[best_from], shoppers[who]) +
                       Dist(shoppers[who], shoppers[best_to]) -
                       Dist(shoppers[best_from], shoppers[best_to]);
        db total_delta = rem_delta + add_delta;
        if (total_delta > -cEps) {
          InsertShopperBetween(who, old_car, old_prev, old_next);
          continue;
        }
        InsertShopperBetween(who, best_car, best_from, best_to);
        improved = true;
        ++improved_times;
        break;
      }
      if (!improved) {
        break;
      }
      if (improved_times >= times) {
        break;
      }
    }
    return improved_times;
  }

  void GreedyEur() {
    std::vector<int> perm;
    perm.reserve(n);
    for (int i = 0; i < n; ++i) {
      perm.push_back(i + 1);
    }
    std::random_device rd;
    std::mt19937 gen(rd());
    auto start = std::chrono::steady_clock::now();
    for (int i = 0; i < cGredTimes; ++i) {
      std::shuffle(perm.begin(), perm.end(), gen);
      try {
        OneGreedyEur(perm);
      }
      catch (const std::exception& e) {
        continue;
      }
      Resolve(perm);
      FindAns();
      SetBetter();
      auto end = std::chrono::steady_clock::now();
      auto duration = std::chrono::duration_cast<std::chrono::seconds>(end - start);
      if (duration.count() > cMaxGredTime) {
        break;
      }
    }
  }

 public:
  VRPSolver(std::string path, std::ostringstream& out) {
    InputData(path);
    begins.resize(v, 0);
    ends.resize(v, 0);
    GreedyEur();
    OutputData(out);
  }
};
