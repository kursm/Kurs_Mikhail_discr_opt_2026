#include <algorithm>
#include <cassert>
#include <chrono>
#include <cmath>
#include <iomanip>
#include <iostream>
#include <fstream>
#include <queue>
#include <random>
#include <set>
#include <sstream>
#include <stack>
#include <stdexcept>
#include <string>
#include <vector>

struct TSPSolver {
 private:
  using db = long double;
  using Pair = std::pair<db, db>;
  using SPair = std::pair<db, int>;
  using VecPair = std::pair<int, int>;
  using Ans = std::pair<std::vector<int>, db>;
  std::vector<Pair> points;
  int num_of_points;
  int LinKerniganMaxSearch = 10;
  int LinKerniganMaxNeib = 1000;
  int TabuLinKerniganMaxTime = 3;
  double cEps = 1E-2;

  db Dist(int num1, int num2) {
    db x_sq = points[num1].first - points[num2].first;
    db y_sq = points[num1].second - points[num2].second;
    return std::sqrt(x_sq * x_sq + y_sq * y_sq);
  }

  db FindDist(std::vector<int>& perm) {
    db ans = 0;
    for (size_t i = 0; i < perm.size() - 1; ++i) {
      ans += Dist(perm[i], perm[i + 1]);
    }
    ans += Dist(perm[0], perm.back());
    return ans;
  }

  void MakeBetter(Ans& other) {
    if (other.second < best_known.second) {
      std::swap(other, best_known);
    }
  }

  int GetNumOfBranches(int depth, int type) {
    const int arr1[10] = {12, 8, 4, 2, 2, 1, 1, 1, 1, 1};
    //const int arr1[10] = {16, 11, 8, 4, 1, 1, 1, 1, 1, 1};
    const int arr2[10] = {8, 6, 3, 1, 1, 1, 1, 1, 1, 1};
    if (num_of_points < 250) {
      return arr1[depth];
    }
    return arr2[depth];
  }

  void AcceptEdge(int& v, int& w, int& new_w, int& new_from,
      std::vector<VecPair>& cycle, db& total_delta, db& len_delta,
      std::stack<std::pair<int, VecPair>>& changes) {
    int fut_w = cycle[new_w].second;
    if (fut_w == new_from) {
      fut_w = cycle[new_w].first;
    }
    total_delta += len_delta;
    changes.push(std::make_pair(w, cycle[w]));
    changes.push(std::make_pair(v, cycle[v]));
    changes.push(std::make_pair(new_w, cycle[new_w]));
    changes.push(std::make_pair(fut_w, cycle[fut_w]));
    VecPair w_swap = cycle[w];
    VecPair v_swap = cycle[v];
    VecPair new_w_swap = cycle[new_w];
    VecPair fut_w_swap = cycle[fut_w];
    if (w_swap.first == v) {
      w_swap.first = fut_w;
    } else {
      w_swap.second = fut_w;
    }
    if (v_swap.first == w) {
      v_swap.first = new_w;
    } else {
      v_swap.second = new_w;
    }
    if (new_w_swap.first == fut_w) {
      new_w_swap.first = v;
    } else {
      new_w_swap.second = v;
    }
    if (fut_w_swap.first == new_w) {
      fut_w_swap.first = w;
    } else {
      fut_w_swap.second = w;
    }
    cycle[w] = w_swap;
    cycle[v] = v_swap;
    cycle[new_w] = new_w_swap;
    cycle[fut_w] = fut_w_swap;
    v = fut_w;
  }

  char LinKerniganStep(int depth, int type, int& v, int& w, std::vector<VecPair>& cycle,
                       db& total_delta, std::stack<std::pair<int, VecPair>>& changes) {
    if (depth >= LinKerniganMaxSearch) {
      return 3;
    }
    int prev_w = v;
    int cur_w = w;
    int max_steps = std::min(LinKerniganMaxNeib, num_of_points);
    std::priority_queue<std::tuple<db, int, int>> variant;
    int num_of_vars = GetNumOfBranches(depth, type);
    if (num_of_vars <= 0) {
      return 0;
    }
    for (int i = 0; i < max_steps; ++i) {
      int fut_w = cycle[cur_w].second;
      if (fut_w == prev_w) {
        fut_w = cycle[cur_w].first;
      }
      if (fut_w == v) {
        break;
      }
      if (i > 0) {
        db len_delta = Dist(v, cur_w) - Dist(v, w) - Dist(fut_w, cur_w) +
                       Dist(fut_w, w);
        variant.push(std::make_tuple(len_delta, cur_w, prev_w));
        if (static_cast<int>(variant.size()) > num_of_vars) {
          variant.pop();
        }
      }
      int next_w = cycle[cur_w].second;
      if (next_w == prev_w) {
        next_w = cycle[cur_w].first;
      }
      prev_w = cur_w;
      cur_w = next_w;
      if (cur_w == v) {
        break;
      }
    }
    if (variant.empty()) {
      return 0;
    }
    std::vector<std::tuple<db, int, int>> vars;
    vars.reserve(variant.size());
    while (!variant.empty()) {
      vars.push_back(variant.top());
      variant.pop();
    }
    db best_total_delta = total_delta;
    int best_id = -1;
    for (int id = static_cast<int>(vars.size()) - 1; id >= 0; --id) {
      db len_delta = std::get<0>(vars[size_t(id)]);
      int new_w = std::get<1>(vars[size_t(id)]);
      int new_from = std::get<2>(vars[size_t(id)]);
      int fut_w = cycle[new_w].second;
      if (fut_w == new_from) {
        fut_w = cycle[new_w].first;
      }
      if (fut_w == v) {
        continue;
      }
      size_t old_size = changes.size();
      db old_total_delta = total_delta;
      int old_v = v;
      AcceptEdge(v, w, new_w, new_from, cycle, total_delta, len_delta, changes);
      LinKerniganStep(depth + 1, type, v, w, cycle, total_delta, changes);
      if (total_delta < best_total_delta) {
        best_total_delta = total_delta;
        best_id = id;
      }
      while (changes.size() > old_size) {
        cycle[changes.top().first] = changes.top().second;
        changes.pop();
      }
      total_delta = old_total_delta;
      v = old_v;
    }
    if (best_total_delta >= -cEps) {
      return 2;
    }
    if (best_id == -1) {
      total_delta = best_total_delta;
      return 1;
    }
    db len_delta = std::get<0>(vars[size_t(best_id)]);
    int new_w = std::get<1>(vars[size_t(best_id)]);
    int new_from = std::get<2>(vars[size_t(best_id)]);
    AcceptEdge(v, w, new_w, new_from, cycle, total_delta, len_delta, changes);
    if (total_delta < -cEps) {
      return 1;
    }
    LinKerniganStep(depth + 1, type, v, w, cycle, total_delta, changes);
    if (total_delta < -cEps) {
      return 1;
    }
    return 2;
  }
  
  bool LinKernigan(std::vector<int>& path) {
    std::vector<VecPair> cycle(num_of_points);
    for (int i = 0; i < num_of_points; ++i) {
      int cur = path[i];
      int prev = path[(i - 1 + num_of_points) % num_of_points];
      int next = path[(i + 1) % num_of_points];
      cycle[cur] = VecPair(prev, next);
    }
    bool had_changes = false;
    bool round_improved = false;
    auto start = std::chrono::steady_clock::now();
    int iteration_num = 0;
    do {
      auto end = std::chrono::steady_clock::now();
      auto duration = std::chrono::duration_cast<std::chrono::seconds>(end - start);
      if (duration.count() > TabuLinKerniganMaxTime) {
        std::cout << "TSP breaked\n";
        break;
      }
      round_improved = false;
      for (int start = 0; start < 2 * num_of_points; ++start) {
        int v = path[start / 2];
        int w = (start % 2 == 0 ? cycle[v].first : cycle[v].second);
        std::stack<std::pair<int, VecPair>> changes;
        db total_delta = 0;
        db start_edge = Dist(v, w);
        char status = LinKerniganStep(0, 0, v, w, cycle, total_delta, changes);
        if (status != 1) {
          continue;
        }
        ++iteration_num;
        had_changes = true;
        round_improved = true;
      }
    } while (round_improved);
    if (!had_changes) {
      return false;
    }
    //std::cout << "iteration num: " << iteration_num << " " << all_iters << " " << tabu_succ << "\n";
    std::vector<bool> used(num_of_points, false);
    int begin = path[0];
    int prev = cycle[begin].first;
    int cur = begin;
    for (int i = 0; i < num_of_points; ++i) {
      if (used[cur]) {
        return false;
      }
      used[cur] = true;
      int nxt = cycle[cur].first;
      if (nxt == prev) {
        nxt = cycle[cur].second;
      }
      prev = cur;
      cur = nxt;
    }
    if (cur != begin) {
      return false;
    }
    prev = cycle[begin].first;
    cur = begin;
    for (int i = 0; i < num_of_points; ++i) {
      path[i] = cur;
      int nxt = cycle[cur].first;
      if (nxt == prev) {
        nxt = cycle[cur].second;
      }
      prev = cur;
      cur = nxt;
    }
    return true;
  }

  void RunLinKernigan() {
    Ans candidate = best_known;
    if (!LinKernigan(candidate.first)) {
      //std::cout << "nothing :(\n";
      return;
    }
    candidate.second = FindDist(candidate.first);
    MakeBetter(candidate);
  }

  void StartFromZero() {
    int zero_index = 0;
    while (best_known.first[zero_index] != 0) {
      ++zero_index;
    }
    std::vector<int> new_path;
    for (int i = 0; i < num_of_points; ++i) {
      int j = (zero_index + i) % num_of_points;
      new_path.push_back(best_known.first[j]);
    }
    best_known.first = new_path;
  }

 public:

  Ans best_known;

  void InputData(std::vector<Pair>& input_points) {
    points = input_points;
    num_of_points = static_cast<int>(points.size());
    best_known = Ans();
  }

  void Solve(bool need_greedy = false) {
    //std::cout << "num of points: " << num_of_points << std::endl;
    Ans eur;
    eur.first.reserve(num_of_points);
    for (int i = 0; i < num_of_points; ++i) {
      eur.first.push_back(i);
    }
    eur.second = FindDist(eur.first);
    best_known = eur;
    RunLinKernigan();
    StartFromZero();
  }
  
  TSPSolver() = default;

};

struct VRPSolver {
 private:

  struct Shopper;
  using db = long double;
  using Ans = std::vector<std::vector<int>>;
  using SPair = std::pair<db, int>;
  static inline const db cInfty = 1E8;
  static inline const int cIntInfty = 1E6;
  db cEps = 0.01;
  int n = 0;
  int v = 0;
  int cGredTimes = 10000;
  int cMaxGredTime = 10;
  int cMaxTspGredTime = 60;
  int cMaxMiss = 1000;
  int calls = 0;
  int pop_size = 20;
  int crossovers_num = 15;
  int pop_lifetime = 40;
  int max_replace = 10;
  int max_K = 10;
  int losts_num = 400;
  int tabu_wait = 2;
  double secs = 0;
  long long time = 0;
  db c = 0;
  db cur_ans_val;
  db best_ans_val = cInfty;
  db mutate_prob = 0.1;
  db replace_prob = 0.2;
  db percent = 0.30;
  std::vector<db> cur_demand;
  std::vector<int> begins;
  std::vector<int> ends;
  std::vector<int> tabu_list;
  std::vector<std::vector<int>> best_ans;
  std::vector<std::vector<std::vector<int>>> population;
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
    shoppers.reserve(n);
    for (int i = 0; i < n; ++i) {
      db demand;
      db x;
      db y;
      input_file >> demand >> x >> y;
      shoppers.push_back(Shopper(x, y, demand, i == 0));
    }
    --n;
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
    std::ofstream output_file("output.txt");
    output_file << out.str();
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
    std::mt19937 gen(228);
    auto start = std::chrono::steady_clock::now();
    //int counter = 0;
    int i = 0;
    while (true) {
      std::shuffle(perm.begin(), perm.end(), gen);
      //++counter;
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
      if ((i >= cGredTimes) && (duration.count() >= 2)) {
        break;
      }
      ++i;
    }
    //std::cout << "counter is: " << counter << std::endl;
  }

  bool RunTspForOneCar(int car) {
    auto start = std::chrono::steady_clock::now();
    std::vector<int> car_path = {0};
    std::vector<std::pair<db, db>> points = {{shoppers[0].x, shoppers[0].y}};
    int cur = begins[car];
    while (cur != 0) {
      car_path.push_back(cur);
      points.push_back({shoppers[cur].x, shoppers[cur].y});
      cur = shoppers[cur].next;
    }
    TSPSolver tsp_solver;
    tsp_solver.InputData(points);
    tsp_solver.Solve();
    std::vector<int>& tsp_order = tsp_solver.best_known.first;
    bool changed = false;
    for (size_t i = 0; i < tsp_order.size(); ++i) {
      changed = changed || tsp_order[i] != static_cast<int>(i);
    }
    tsp_order.push_back(0);
    begins[car] = car_path[tsp_order[1]];
    ends[car] = car_path[tsp_order[tsp_order.size() - 2]];
    for (size_t i = 1; i + 1 < tsp_order.size(); ++i) {
      int shopper = car_path[tsp_order[i]];
      shoppers[shopper].prev = car_path[tsp_order[i - 1]];
      shoppers[shopper].next = car_path[tsp_order[i + 1]];
      shoppers[shopper].is_beg = false;
      shoppers[shopper].is_end = false;
    }
    shoppers[begins[car]].is_beg = true;
    shoppers[ends[car]].is_end = true;
    auto end = std::chrono::steady_clock::now();
    auto duration = std::chrono::duration_cast<std::chrono::milliseconds>(end - start);
    ++calls;
    secs += static_cast<double>(duration.count()) / 1000.0f;
    return changed;
  }

  bool SolveTsp() {
    bool improved = false;
    for (int car = 0; car < v; ++car) {
      improved = RunTspForOneCar(car) || improved;
    }
    if (improved) {
      std::cout << "!";
    } else {
      std::cout << ".";
    }
    return improved;
  }

  void SetBestAsCur() {
    ClearShoppers();
    begins.assign(v, 0);
    ends.assign(v, 0);
    for (int i = 0; i < static_cast<int>(shoppers.size()); ++i) {
      shoppers[i].is_beg = false;
      shoppers[i].is_end = false;
    }
    for (int car = 0; car < v; ++car) {
      int prev = 0;
      for (size_t i = 1; i + 1 < best_ans[car].size(); ++i) {
        int shopper = best_ans[car][i];
        InsertShopperBetween(shopper, car, prev, 0);
        prev = shopper;
      }
    }
    cur_ans_val = best_ans_val;
  }

  void TspAndGreedy() {
    SetBestAsCur();
    std::vector<int> perm;
    perm.reserve(n);
    for (int i = 0; i < n; ++i) {
      perm.push_back(i + 1);
    }
    std::random_device rd;
    std::mt19937 gen(rd());
    auto start = std::chrono::steady_clock::now();
    SolveTsp();
    int misses = 0;
    while(true) {
      auto end = std::chrono::steady_clock::now();
      auto duration = std::chrono::duration_cast<std::chrono::seconds>(end - start);
      if (duration.count() > cMaxTspGredTime) {
        std::cout << "TspAndGreedy breaked!" << std::endl;
        break;
      }
      std::shuffle(perm.begin(), perm.end(), gen);
      bool is_done = Resolve(perm) != 0;
      if (!is_done) {
        ++misses;
      } else {
        misses = 0;
        SolveTsp();
      }
      if (misses > cMaxMiss) {
        break;
      }
    }
    FindAns();
    SetBetter();
  }

  void GenPopulation() {
    population.clear();
    std::random_device rd;
    std::mt19937 gen(rd());
    std::vector<int> perm(n);
    for (int j = 0; j < n; ++j) {
      perm[j] = j + 1;
    }
    for (int i = 0; i < pop_size; ++i) {
      std::vector<std::vector<int>> classes(v);
      std::vector<db> class_wei(v, 0);
      std::shuffle(perm.begin(), perm.end(), gen);
      for (int car = 0; car < v; ++car) {
        int shopper = perm[car];
        classes[car].push_back(shopper);
        class_wei[car] += shoppers[shopper].demand;
      }
      bool success = true;
      for (int j = v; j < n; ++j) {
        int shopper = perm[j];
        int best_class = -1;
        db best_dist = cInfty;
        for (int car = 0; car < v; ++car) {
          if (class_wei[car] + shoppers[shopper].demand > c) {
            continue;
          }
          db first_dist = Dist(shoppers[shopper], shoppers[0]);
          db second_dist = cInfty;
          for (int other : classes[car]) {
            db dist = Dist(shoppers[shopper], shoppers[other]);
            if (dist < first_dist) {
              second_dist = first_dist;
              first_dist = dist;
            } else if (dist < second_dist) {
              second_dist = dist;
            }
          }
          db dist_sum = first_dist + second_dist;
          if (dist_sum < best_dist) {
            best_dist = dist_sum;
            best_class = car;
          }
        }
        if (best_class == -1) {
          //std::cout << "Did not found the ending!" << std::endl;
          --i;
          success = false;
          break;
        }
        classes[best_class].push_back(shopper);
        class_wei[best_class] += shoppers[shopper].demand;
      }
      if (success) {
        population.push_back(classes);
        GroupSetBetter(classes);
      }
    }
  }

  db GetMetric(int place) {
    db result = 0;
    for (int car = 0; car < v; ++car) {
      std::vector<std::pair<db, db>> points;
      points.push_back({shoppers[0].x, shoppers[0].y});
      for (int shopper : population[place][car]) {
        points.push_back({shoppers[shopper].x, shoppers[shopper].y});
      }
      TSPSolver tsp_solver;
      tsp_solver.InputData(points);
      tsp_solver.Solve();
      result += tsp_solver.best_known.second;
    }
    return result;
  }

  Ans Crossover(int ft, int sc, std::vector<db>& class_wei) {
    class_wei.assign(v, 0);
    std::vector<std::tuple<int, int, int>> inter;
    inter.reserve(n);
    for (int i = 0; i < n; ++i) {
      inter.push_back({0, 0, i + 1});
    }
    for (int group = 0; group < v; ++group) {
      for (int i = 0; i < population[ft][group].size(); ++i) {
        std::get<0>(inter[population[ft][group][i] - 1]) = group;
      }
      for (int i = 0; i < population[sc][group].size(); ++i) {
        std::get<1>(inter[population[sc][group][i] - 1]) = group;
      }
    }
    std::sort(inter.begin(), inter.end());
    std::vector<std::vector<int>> inter_size(v, std::vector<int>(v, 0));
    std::vector<std::vector<db>> inter_demand(v, std::vector<db>(v, 0));
    std::vector<std::vector<int>> class_start(v, std::vector<int>(v, -1));
    for (int i = 0; i < inter.size(); ++i) {
      const auto& triple = inter[i];
      int mom = std::get<0>(triple);
      int dad = std::get<1>(triple);
      int shopper = std::get<2>(triple);
      if (class_start[mom][dad] == -1) {
        class_start[mom][dad] = i;
      }
      ++inter_size[mom][dad];
      inter_demand[mom][dad] += shoppers[shopper].demand;
    }
    std::set<std::tuple<db, int, int>, std::greater<std::tuple<db, int, int>>> remaining;
    for (int mom = 0; mom < v; ++mom) {
      for (int dad = 0; dad < v; ++dad) {
        if (inter_size[mom][dad] > 0) {
          remaining.insert({inter_demand[mom][dad], mom, dad});
        }
      }
    }
    std::vector<int> mom_car(v);
    std::set<int> unused;
    for (int i = 0; i < v; ++i) {
      mom_car[i] = i;
      unused.insert(i);
    }
    std::mt19937 gen(67);
    std::shuffle(mom_car.begin(), mom_car.end(), gen);
    std::vector<int> dad_car(v);
    std::vector<std::vector<int>> class_car(v, std::vector<int>(v, -1));
    for (int i = 0; i < mom_car.size(); ++i) {
      int best_dad = -1;
      int best_size = -1;
      for (auto it = unused.begin(); it != unused.end(); ++it) {
        int dad = *it;
        if (inter_size[mom_car[i]][dad] > best_size) {
          best_size = inter_size[mom_car[i]][dad];
          best_dad = dad;
        }
      }
      dad_car[best_dad] = mom_car[i];
      class_car[mom_car[i]][best_dad] = mom_car[i];
      class_wei[mom_car[i]] += inter_demand[mom_car[i]][best_dad];
      remaining.erase({inter_demand[mom_car[i]][best_dad], mom_car[i], best_dad});
      unused.erase(best_dad);
    }
    std::uniform_int_distribution<int> coin(0, 1);
    std::vector<std::pair<int, int>> problem_classes;
    for (auto it = remaining.begin(); it != remaining.end(); ++it) {
      db demand = std::get<0>(*it);
      int mom = std::get<1>(*it);
      int dad = std::get<2>(*it);
      int mom_car_num = mom;
      int dad_car_num = dad_car[dad];
      bool can_mom = class_wei[mom_car_num] + demand <= c;
      bool can_dad = class_wei[dad_car_num] + demand <= c;
      int car = -1;
      if (can_mom && can_dad) {
        car = (coin(gen) == 0 ? mom_car_num : dad_car_num);
      } else if (can_mom) {
        car = mom_car_num;
      } else if (can_dad) {
        car = dad_car_num;
      }
      if (car == -1) {
        problem_classes.push_back({mom, dad});
        continue;
      }
      class_car[mom][dad] = car;
      class_wei[car] += demand;
    }
    Ans child(v);
    for (int i = 0; i < inter.size(); ++i) {
      int mom = std::get<0>(inter[i]);
      int dad = std::get<1>(inter[i]);
      int shopper = std::get<2>(inter[i]);
      int car = class_car[mom][dad];
      if (car != -1) {
        child[car].push_back(shopper);
      }
    }
    for (int i = 0; i < problem_classes.size(); ++i) {
      int mom = problem_classes[i].first;
      int dad = problem_classes[i].second;
      int pos = class_start[mom][dad];
      while (pos < inter.size() && std::get<0>(inter[pos]) == mom &&
             std::get<1>(inter[pos]) == dad) {
        int shopper = std::get<2>(inter[pos]);
        int best_car = -1;
        db best_dist = cInfty;
        for (int car = 0; car < v; ++car) {
          if (class_wei[car] + shoppers[shopper].demand > c) {
            continue;
          }
          db first_dist = Dist(shoppers[shopper], shoppers[0]);
          db second_dist = cInfty;
          if (child[car].empty()) {
            second_dist = first_dist;
          }
          for (int j = 0; j < child[car].size(); ++j) {
            int other = child[car][j];
            db dist = Dist(shoppers[shopper], shoppers[other]);
            if (dist < first_dist) {
              second_dist = first_dist;
              first_dist = dist;
            } else if (dist < second_dist) {
              second_dist = dist;
            }
          }
          db dist_sum = first_dist + second_dist;
          if (dist_sum < best_dist) {
            best_dist = dist_sum;
            best_car = car;
          }
        }
        if (best_car == -1) {
          throw std::runtime_error("Crossover could not place shopper");
        }
        child[best_car].push_back(shopper);
        class_wei[best_car] += shoppers[shopper].demand;
        ++pos;
      }
    }
    return child;
  }

  db GroupSetBetter(Ans& groups) {
    db metric = 0;
    Ans paths(v);
    for (int car = 0; car < v; ++car) {
      std::vector<std::pair<db, db>> points;
      std::vector<int> car_paths;
      points.push_back({shoppers[0].x, shoppers[0].y});
      car_paths.push_back(0);
      for (int i = 0; i < groups[car].size(); ++i) {
        int shopper = groups[car][i];
        points.push_back({shoppers[shopper].x, shoppers[shopper].y});
        car_paths.push_back(shopper);
      }
      TSPSolver tsp_solver;
      tsp_solver.InputData(points);
      tsp_solver.Solve();
      metric += tsp_solver.best_known.second;
      paths[car].push_back(0);
      for (int i = 1; i < tsp_solver.best_known.first.size(); ++i) {
        int ind = tsp_solver.best_known.first[i];
        paths[car].push_back(car_paths[ind]);
      }
      paths[car].push_back(0);
    }
    if (metric < best_ans_val) {
      best_ans_val = metric;
      best_ans = paths;
    }
    return metric;
  }

  static bool Comp2(SPair first, SPair second) {
    return first.first > second.first;
  }

  void Mutate(Ans& child, std::vector<db>& class_wei) {
    std::random_device rd;
    std::mt19937 gen(rd());
    std::uniform_real_distribution<db> probability(0, 1);
    if (probability(gen) >= mutate_prob) {
      return;
    }
    std::vector<std::pair<int, int>> order;
    for (int car = 0; car < v; ++car) {
      for (int i = 0; i < child[car].size(); ++i) {
        order.push_back({car, child[car][i]});
      }
    }
    int replaced = 0;
    for (int i = 0; i < order.size(); ++i) {
      if (probability(gen) >= replace_prob) {
        continue;
      }
      int old_car = order[i].first;
      int shopper = order[i].second;
      std::vector<int> variants;
      for (int car = 0; car < v; ++car) {
        if (car != old_car &&
            class_wei[car] + shoppers[shopper].demand <= c) {
          variants.push_back(car);
        }
      }
      if (variants.empty()) {
        continue;
      }
      std::uniform_int_distribution<int> car_dist(
          0, static_cast<int>(variants.size()) - 1);
      int new_car = variants[car_dist(gen)];
      int pos = 0;
      while (child[old_car][pos] != shopper) {
        ++pos;
      }
      child[old_car].erase(child[old_car].begin() + pos);
      child[new_car].push_back(shopper);
      class_wei[old_car] -= shoppers[shopper].demand;
      class_wei[new_car] += shoppers[shopper].demand;
      ++replaced;
      if (replaced == max_replace) {
        return;
      }
    }
  }

  void Genetics() {
    GenPopulation();
    std::random_device rd;
    std::mt19937 gen(rd());
    auto start = std::chrono::steady_clock::now();
    for (int it = 0; it < pop_lifetime; ++it) {
      auto end = std::chrono::steady_clock::now();
      auto duration = std::chrono::duration_cast<std::chrono::seconds>(end - start);
      if (duration.count() > 300) {
        break;
      }
      db best_child = cInfty;
      std::vector<Ans> children;
      children.reserve(crossovers_num);
      std::uniform_int_distribution<int> parent_dist(0, static_cast<int>(population.size()) - 1);
      for (int i = 0; i < crossovers_num; ++i) {
        int p1 = parent_dist(gen);
        int p2 = parent_dist(gen);
        while (p2 == p1) {
          p2 = parent_dist(gen);
        }
        try {
          std::vector<db> class_wei;
          Ans child = Crossover(p1, p2, class_wei);
          Mutate(child, class_wei);
          db value = GroupSetBetter(child);
          children.push_back(child);
          if (value < best_child) {
            best_child = value;
          }
        }
        catch (const std::exception& e) {
          std::cout << "#";
          continue;
        } 
      }
      std::cout << "Iteration: " << it << ", best value: " << best_child << std::endl;
      std::vector<SPair> worst;
      worst.reserve(population.size());
      for (size_t i = 0; i < population.size(); ++i) {
        worst.push_back(SPair(GetMetric(i), static_cast<int>(i)));
      }
      std::sort(worst.begin(), worst.end(), Comp2);
      int replace_cnt = std::min(static_cast<int>(children.size()), static_cast<int>(population.size()));
      for (int i = 0; i < replace_cnt; ++i) {
        population[worst[i].second] = children[i];
      }
    }
  }

  bool FindNewBestPlace() {
    bool changed = false;
    while (true) {
      bool improved = false;
      for (int it = 1; it <= n; ++it) {
        int who = it;
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
        changed = true;
        break;
      }
      if (!improved) {
        break;
      }
    }
    return changed;
  }

  void RemoveShopper(int who) {
    int car = shoppers[who].car;
    int prev = shoppers[who].prev;
    int next = shoppers[who].next;
    if (prev == 0) {
      begins[car] = next;
      if (next != 0) {
        shoppers[next].is_beg = true;
      }
    } else {
      shoppers[prev].next = next;
    }
    if (next == 0) {
      ends[car] = prev;
      if (prev != 0) {
        shoppers[prev].is_end = true;
      }
    } else {
      shoppers[next].prev = prev;
    }
    cur_demand[car] -= shoppers[who].demand;
    shoppers[who].car = -1;
    shoppers[who].prev = -1;
    shoppers[who].next = -1;
    shoppers[who].is_beg = false;
    shoppers[who].is_end = false;
  }

  bool SwapTwo() {
    bool changed = false;
    while (true) {
      bool improved = false;
      for (int i = 1; i <= n; ++i) {
        for (int j = i + 1; j <= n; ++j) {
          int car1 = shoppers[i].car;
          int car2 = shoppers[j].car;
          if (car1 != car2) {
            if (cur_demand[car1] + shoppers[j].demand -
                    shoppers[i].demand > c) {
              continue;
            }
            if (cur_demand[car2] + shoppers[i].demand -
                    shoppers[j].demand > c) {
              continue;
            }
          }
          int prev1 = shoppers[i].prev;
          int next1 = shoppers[i].next;
          int prev2 = shoppers[j].prev;
          int next2 = shoppers[j].next;
          bool adjacent = car1 == car2 && (next1 == j || next2 == i);
          db rem_delta;
          db add_delta;
          if (adjacent) {
            int first = (next1 == j ? i : j);
            int second = (next1 == j ? j : i);
            int prev = shoppers[first].prev;
            int next = shoppers[second].next;
            rem_delta = Dist(shoppers[prev], shoppers[first]) +
                        Dist(shoppers[first], shoppers[second]) +
                        Dist(shoppers[second], shoppers[next]);
            add_delta = Dist(shoppers[prev], shoppers[second]) +
                        Dist(shoppers[second], shoppers[first]) +
                        Dist(shoppers[first], shoppers[next]);
          } else {
            rem_delta = Dist(shoppers[prev1], shoppers[i]) +
                        Dist(shoppers[i], shoppers[next1]) +
                        Dist(shoppers[prev2], shoppers[j]) +
                        Dist(shoppers[j], shoppers[next2]);
            add_delta = Dist(shoppers[prev1], shoppers[j]) +
                        Dist(shoppers[j], shoppers[next1]) +
                        Dist(shoppers[prev2], shoppers[i]) +
                        Dist(shoppers[i], shoppers[next2]);
          }
          if (add_delta >= rem_delta - cEps) {
            continue;
          }
          if (adjacent) {
            int first = (next1 == j ? i : j);
            int second = (next1 == j ? j : i);
            int prev = shoppers[first].prev;
            int next = shoppers[second].next;
            RemoveShopper(first);
            RemoveShopper(second);
            InsertShopperBetween(second, car1, prev, next);
            InsertShopperBetween(first, car1, second, next);
          } else {
            RemoveShopper(i);
            RemoveShopper(j);
            InsertShopperBetween(j, car1, prev1, next1);
            InsertShopperBetween(i, car2, prev2, next2);
          }
          improved = true;
          changed = true;
        }
      }
      if (!improved) {
        break;
      }
    }
    return changed;
  }

  bool TwoOpt(int car) {
    bool changed = false;
    while (true) {
      bool improved = false;
      int left = begins[car];
      while (left != 0) {
        int right = shoppers[left].next;
        while (right != 0) {
          int prev = shoppers[left].prev;
          int next = shoppers[right].next;
          db delta = Dist(shoppers[prev], shoppers[right]) +
                     Dist(shoppers[left], shoppers[next]) -
                     Dist(shoppers[prev], shoppers[left]) -
                     Dist(shoppers[right], shoppers[next]);
          if (delta < -cEps) {
            int cur = left;
            while (true) {
              int old_next = shoppers[cur].next;
              shoppers[cur].next = shoppers[cur].prev;
              shoppers[cur].prev = old_next;
              if (cur == right) {
                break;
              }
              cur = old_next;
            }
            if (prev == 0) {
              begins[car] = right;
            } else {
              shoppers[prev].next = right;
            }
            shoppers[right].prev = prev;
            shoppers[right].is_beg = (prev == 0);
            shoppers[right].is_end = false;
            if (next == 0) {
              ends[car] = left;
            } else {
              shoppers[next].prev = left;
            }
            shoppers[left].next = next;
            shoppers[left].is_beg = false;
            shoppers[left].is_end = (next == 0);
            cur_ans_val += delta;
            changed = true;
            improved = true;
            break;
          }
          right = shoppers[right].next;
        }
        if (improved) {
          break;
        }
        left = shoppers[left].next;
      }
      if (!improved) {
        break;
      }
    }
    return changed;
  }

  bool TwoOpt() {
    bool changed = false;
    while(true) {
      bool improved = false;
      for (int i = 0 ; i < v; ++i) {
        improved = improved || TwoOpt(i);
      }
      if (!improved) {
        break;
      }
      changed = true;
    }
    return changed;
  }

  bool Cross(bool can_make_worse = false, bool tabu_on = false) {
    db total_worse = 0;
    bool changed = false;
    while (true) {
      bool improved = false;
      for (int i = 1; i <= n; ++i) {
        for (int j = i + 1; j <= n; ++j) {
          int car1 = shoppers[i].car;
          int car2 = shoppers[j].car;
          if (car1 == car2) {
            continue;
          }
          db first_dem = shoppers[i].demand;
          db second_dem = shoppers[j].demand;
          int cur_first = i;
          int cur_second = j;
          int best_first = -1;
          int best_second = -1;
          db best_delta = cInfty;
          for (int i1 = 0; i1 < max_K; ++i1) {
            cur_second = j;
            second_dem = shoppers[j].demand;
            for (int j1 = 0; j1 < max_K; ++j1) {
              if ((cur_demand[car1] - first_dem + second_dem > c) || 
                  (cur_demand[car2] + first_dem - second_dem > c)) {
                if (shoppers[cur_second].is_end) {
                  break;
                }
                cur_second = shoppers[cur_second].next;
                second_dem += shoppers[cur_second].demand;
                continue;
              }
              int prev1 = shoppers[i].prev;
              int prev2 = shoppers[j].prev;
              int next1 = shoppers[cur_first].next;
              int next2 = shoppers[cur_second].next;
              db rem_delta = Dist(shoppers[prev1], shoppers[i]) +
                             Dist(shoppers[cur_first], shoppers[next1]) +
                             Dist(shoppers[prev2], shoppers[j]) +
                             Dist(shoppers[cur_second], shoppers[next2]);
              db add_delta = Dist(shoppers[prev1], shoppers[j]) +
                             Dist(shoppers[cur_second], shoppers[next1]) +
                             Dist(shoppers[prev2], shoppers[i]) +
                             Dist(shoppers[cur_first], shoppers[next2]);
              if (add_delta - rem_delta < best_delta) {
                best_first = cur_first;
                best_second = cur_second;
                best_delta = add_delta - rem_delta;
              }
              if (shoppers[cur_second].is_end) {
                break;
              }
              cur_second = shoppers[cur_second].next;
              second_dem += shoppers[cur_second].demand;
            }
            if (shoppers[cur_first].is_end) {
              break;
            }
            cur_first = shoppers[cur_first].next;
            first_dem += shoppers[cur_first].demand;
          }
          if ((best_delta >= -cEps) && !can_make_worse) {
            continue;
          }
          if (can_make_worse && tabu_on && (best_delta >= -cEps)) {
            if ((tabu_list[car1] > time) || (tabu_list[car2] > time)) {
              continue;
            }
          }
          if (best_delta >= -cEps) {
            if ((total_worse + best_delta > cur_ans_val * percent) || (best_first == -1)) {
              continue;
            }
            total_worse += std::max(best_delta, db(0));
          }
          int prev1 = shoppers[i].prev;
          int next1 = shoppers[best_first].next;
          int prev2 = shoppers[j].prev;
          int next2 = shoppers[best_second].next;
          db best_first_dem = 0;
          db best_second_dem = 0;
          int cur = i;
          while (true) {
            shoppers[cur].car = car2;
            best_first_dem += shoppers[cur].demand;
            if (cur == best_first) {
              break;
            }
            cur = shoppers[cur].next;
          }
          cur = j;
          while (true) {
            shoppers[cur].car = car1;
            best_second_dem += shoppers[cur].demand;
            if (cur == best_second) {
              break;
            }
            cur = shoppers[cur].next;
          }
          cur_demand[car1] += best_second_dem - best_first_dem;
          cur_demand[car2] += best_first_dem - best_second_dem;
          shoppers[i].is_beg = false;
          shoppers[best_first].is_end = false;
          shoppers[j].is_beg = false;
          shoppers[best_second].is_end = false;
          if (prev1 == 0) {
            begins[car1] = j;
          } else {
            shoppers[prev1].next = j;
          }
          shoppers[j].prev = prev1;
          shoppers[j].is_beg = (prev1 == 0);
          if (next1 == 0) {
            ends[car1] = best_second;
          } else {
            shoppers[next1].prev = best_second;
          }
          shoppers[best_second].next = next1;
          shoppers[best_second].is_end = (next1 == 0);
          if (prev2 == 0) {
            begins[car2] = i;
          } else {
            shoppers[prev2].next = i;
          }
          shoppers[i].prev = prev2;
          shoppers[i].is_beg = (prev2 == 0);
          if (next2 == 0) {
            ends[car2] = best_first;
          } else {
            shoppers[next2].prev = best_first;
          }
          shoppers[best_first].next = next2;
          shoppers[best_first].is_end = (next2 == 0);
          cur_ans_val += best_delta;
          improved = true;
          changed = true;
          tabu_list[car1] = time + tabu_wait;
          tabu_list[car2] = time + tabu_wait;
          ++time;
        }
      }
      if (!improved || can_make_worse) {
        break;
      }
    }
    return changed;
  }

  void LocalSearch() {
    auto start = std::chrono::steady_clock::now();
    int losts = 0;
    while(true) {
      bool done = false;
      done = done || FindNewBestPlace();
      done = done || SwapTwo();
      done = done || TwoOpt();
      done = done || Cross();
      if (!done) {
        ++losts;
        FindAns();
        SetBetter();
        if (losts > losts_num) {
          break;
        }
        auto end = std::chrono::steady_clock::now();
        auto duration = std::chrono::duration_cast<std::chrono::seconds>(end - start);
        if (duration.count() > 120) {
          std::cout << "BREAKED" << std::endl;
          break;
        }
        if(!Cross(true)) {
          break;
        }
      }
    }
  }

  void LocalSearchWithTabu() {
    auto start = std::chrono::steady_clock::now();
    tabu_list.assign(v, -1);
    int losts = 0;
    while(true) {
      bool done = false;
      done = done || FindNewBestPlace();
      done = done || SwapTwo();
      done = done || TwoOpt();
      done = done || Cross();
      if (!done) {
        ++losts;
        FindAns();
        SetBetter();
        if (losts > losts_num) {
          break;
        }
        auto end = std::chrono::steady_clock::now();
        auto duration = std::chrono::duration_cast<std::chrono::seconds>(end - start);
        if (duration.count() > 120) {
          std::cout << "BREAKED" << std::endl;
          break;
        }
        if (!Cross(true, true)) {
          if (!Cross(true, false)) {
            break;
          }
        }
      }
    }
  }

 public:
  VRPSolver(std::string path, std::ostringstream& out) {
    InputData(path);
    begins.resize(v, 0);
    ends.resize(v, 0);
    GreedyEur();
    
    //TspAndGreedy();
    //Genetics();
    
    SetBestAsCur();
    //LocalSearch();
    LocalSearchWithTabu();

    OutputData(out);
  }
};
