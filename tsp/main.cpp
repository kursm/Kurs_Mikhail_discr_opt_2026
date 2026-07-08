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

struct TSPSolver{
 private:
  using db = long double;
  using Pair = std::pair<db, db>;
  using SPair = std::pair<db, int>;
  using VecPair = std::pair<int, int>;
  using Ans = std::pair<std::vector<int>, db>;
  std::vector<Pair> points;
  std::vector<std::vector<int>> sort_order;
  std::vector<Ans> population;
  std::vector<std::set<int>> is_neib;
  std::vector<std::set<SPair>> sr_neib;
  int num_of_points;
  int FastLinKerniganIter = 250;
  int LinKerniganMaxSearch = 10;
  int LinKerniganMaxNeib = 2000;
  int crossovers_num = 10;
  int population_size = 20;
  int time_to_change = 100;
  static inline int small_window_size = 7;
  static inline int greedy_window_size = 2000;
  static inline int two_opt_window_size = 5000;
  static inline int three_opt_window_size = 150;
  static inline int pop_rebuild_min_num = 100;
  static inline int pop_annealing_retry = 1;
  bool sort_order_is_set = false;
  double cEps = 1E-2  ;
  double conver_coef = 0.225;
  double mut_prob = 0.55;
  double min_mut_prob = 0.098;
  double change = 0.15;
  double destroy = 0.015;
  long double temp;
  long double temp_change = 0.9999;
  long double temp_stop = 1E-8;
  long double ptemp = 1E5;
  long double ptemp_change = 0.995;
  long double ptemp_stop = 1E-4;
  db cInfty = 1E10;
  Ans annelcur;
  Ans popcur;

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

  static bool Comp2(SPair first, SPair second) {
    return first.first > second.first;
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
    auto start = std::chrono::steady_clock::now();
    for (int iter = 0; iter < two_opt_iters; ++iter) {
      auto end = std::chrono::steady_clock::now();
      auto duration = std::chrono::duration_cast<std::chrono::seconds>(end - start);
      if (duration.count() > 60) {
        std::cout << "iter is: " << iter << "\n";
        break;
      }
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
        //std::cout << "num_of_iters:" << iter << "\n";
        break;
      }
    }
    return ans;
  }

  void OutAns(std::ostringstream& out) {
    std::ofstream output_file("output.txt");
    out << std::fixed << std::setprecision(5) << best_known.second << "\n";
    output_file << std::fixed << std::setprecision(5) << best_known.second << "\n";
    //std::cout << "Answer is: ";
    for (size_t i = 0; i < best_known.first.size(); ++i) {
      //std::cout << best_known.first[i] << " ";
      out << best_known.first[i] << " ";
      output_file << best_known.first[i] << " ";
    }
    //std::cout << "\n";
    out << "\n";
    output_file << "\n";
  }

  void MakeBetter(Ans& other) {
    if (other.second < best_known.second) {
      std::swap(other, best_known);
    }
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
    do {
      auto end = std::chrono::steady_clock::now();
      auto duration = std::chrono::duration_cast<std::chrono::seconds>(end - start);
      if (duration.count() > 120) {
        break;
      }
      round_improved = false;
      for (int start = 0; start < 2 * num_of_points; ++start) {
        int v = path[start / 2];
        int w = (start % 2 == 0 ? cycle[v].first : cycle[v].second);
        std::stack<std::pair<int, VecPair>> changes;
        db total_delta = 0;
        for (int iter = 0; iter < LinKerniganMaxSearch; ++iter) {
          int new_w = -1;
          int new_from = -1;
          db best_delta = 0;
          bool has_candidate = false;
          int prev_w = v;
          int cur_w = w;
          int max_steps = std::min(LinKerniganMaxNeib, num_of_points);
          for (int i = 0; i < max_steps; ++i) {
            int fut_w = cycle[cur_w].second;
            if (fut_w == prev_w) {
              fut_w = cycle[cur_w].first;
            }
            if (fut_w == v) {
              break;
            }
            db len_delta = Dist(v, cur_w) - Dist(v, w) - Dist(fut_w, cur_w) +
                           Dist(fut_w, w);
            if (i > 0 && (!has_candidate || len_delta < best_delta)) {
              best_delta = len_delta;
              new_w = cur_w;
              new_from = prev_w;
              has_candidate = true;
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
          if (new_w == -1) {
            break;
          }
          int fut_w = cycle[new_w].second;
          if (fut_w == new_from) {
            fut_w = cycle[new_w].first;
          }
          if (fut_w == v) {
            break;
          }
          total_delta += Dist(v, new_w) - Dist(v, w) - Dist(fut_w, new_w) +
                         Dist(fut_w, w);
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
          if (total_delta < -cEps) {
            break;
          }
        }
        if (total_delta >= -cEps) {
          while (!changes.empty()) {
            cycle[changes.top().first] = changes.top().second;
            changes.pop();
          }
          continue;
        }
        if (!changes.empty()) {
          had_changes = true;
          round_improved = true;
        }
      }
    } while (round_improved);
    if (!had_changes) {
      return false;
    }
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

  void RunKernigan() {
    Ans candidate = best_known;
    if (!LinKernigan(candidate.first)) {
      std::cout << "nothing :(\n";
      return;
    }
    //std::cout << "Done!" << "\n";
    candidate.second = FindDist(candidate.first);
    MakeBetter(candidate);
  }

  void GenPopulation() {
    population.clear();
    population.reserve(population_size);
    std::random_device rd;
    std::mt19937 gen(rd());
    std::uniform_int_distribution<int> dist(0, num_of_points - 1);
    for (int i = 0; i < population_size; ++i) {
      int first = dist(gen);
      Ans cur;
      if (num_of_points < cMaxForSort) {
        cur = ClosestEur(first);
      } else {
        cur = ClosestEur2(first);
      }
      LinKernigan(cur.first);
      cur.second = FindDist(cur.first);
      std::vector<int> next_vertex(num_of_points, -1);
      for (int j = 0; j < num_of_points; ++j) {
        int u = cur.first[j];
        int v = cur.first[(j + 1) % num_of_points];
        next_vertex[u] = v;
      }
      cur.first.swap(next_vertex);
      population.push_back(cur);
    }
  }

  bool Converged() {
    if (population.empty()) {
      return true;
    }
    std::random_device rd;
    std::mt19937 gen(rd());
    std::uniform_int_distribution<int> pick_ref(0, static_cast<int>(population.size()) - 1);
    int ref_id = pick_ref(gen);
    double max_allowed = conver_coef * num_of_points;
    double average_diff = 0;
    for (size_t i = 0; i < population.size(); ++i) {
      int diff = 0;
      for (int v = 0; v < num_of_points; ++v) {
        if (population[ref_id].first[v] != population[i].first[v]) {
          ++diff;
        }
      }
      average_diff += diff;
      if (diff > max_allowed) {
        return false;
      }
    }
    //std::cout << "avg diff: " << (average_diff / static_cast<db> (num_of_points)) << "\n";
    return true;
  }

  std::vector<std::pair<int, bool>> CycleMaker(std::vector<VecPair>& begs) {
    std::vector<std::pair<int, bool>> answer;
    std::vector<bool> is_used(begs.size(), false);
    answer.reserve(begs.size());
    is_used[0] = true;
    answer.push_back({0, true});
    int cur_vertex = begs[0].second;
    for (size_t iter = 1; iter < begs.size(); ++iter) {
      int best_id = -1;
      bool take_first = true;
      db best_dist = cInfty;
      for (size_t i = 0; i < begs.size(); ++i) {
        if (is_used[i]) {
          continue;
        }
        db dist_to_first = Dist(cur_vertex, begs[i].first);
        if (dist_to_first < best_dist) {
          best_dist = dist_to_first;
          best_id = static_cast<int>(i);
          take_first = true;
        }
        db dist_to_second = Dist(cur_vertex, begs[i].second);
        if (dist_to_second < best_dist) {
          best_dist = dist_to_second;
          best_id = static_cast<int>(i);
          take_first = false;
        }
      }
      if (best_id == -1) {
        break;
      }
      is_used[best_id] = true;
      answer.push_back({best_id, take_first});
      if (take_first) {
        cur_vertex = begs[best_id].second;
      } else {
        cur_vertex = begs[best_id].first;
      }
    }
    return answer;
  }

  Ans DPX(int first, int second) {
    int mismatch = -1;
    for (int v = 0; v < num_of_points; ++v) {
      if (population[first].first[v] != population[second].first[v]) {
        mismatch = population[second].first[v];
        break;
      }
    }
    if (mismatch == -1) {
      return population[first];
    }
    std::vector<std::vector<int>> parts;
    std::vector<VecPair> begs;
    int start_vertex = mismatch;
    int cur = start_vertex;
    std::vector<int> cur_part;
    for (int i = 0; i < num_of_points; ++i) {
      cur_part.push_back(cur);
      if (population[first].first[cur] != population[second].first[cur]) {
        begs.push_back(VecPair(cur_part.front(), cur_part.back()));
        parts.push_back(cur_part);
        cur_part.clear();
      }
      cur = population[first].first[cur];
    }
    if (!cur_part.empty()) {
      begs.push_back(VecPair(cur_part.front(), cur_part.back()));
      parts.push_back(cur_part);
    }
    std::vector<std::pair<int, bool>> order = CycleMaker(begs);
    std::vector<int> child_path;
    child_path.reserve(num_of_points);
    for (size_t i = 0; i < order.size(); ++i) {
      int part_id = order[i].first;
      bool from_first = order[i].second;
      if (from_first) {
        for (size_t j = 0; j < parts[part_id].size(); ++j) {
          child_path.push_back(parts[part_id][j]);
        }
      } else {
        for (int j = static_cast<int>(parts[part_id].size()) - 1; j >= 0; --j) {
          child_path.push_back(parts[part_id][j]);
        }
      }
    }
    LinKernigan(child_path);
    Ans child;
    child.first.assign(num_of_points, -1);
    for (int i = 0; i < num_of_points; ++i) {
      child.first[child_path[i]] = child_path[(i + 1) % num_of_points];
    }
    child.second = FindDist(child_path);
    if (child.second < best_known.second) {
      best_known.first = child_path;
      best_known.second = child.second;
    }
    return child;
  }

  void Mutation(Ans& ans) {
    std::random_device rd;
    std::mt19937 gen(rd());
    std::uniform_int_distribution<int> split_two(2, num_of_points - 2);
    int sum_part1 = split_two(gen);
    int sum_part2 = num_of_points - sum_part1;
    std::uniform_int_distribution<int> split_12(1, sum_part1 - 1);
    int len1 = split_12(gen);
    int len2 = sum_part1 - len1;
    std::uniform_int_distribution<int> split_34(1, sum_part2 - 1);
    int len3 = split_34(gen);
    int len4 = sum_part2 - len3;
    std::uniform_int_distribution<int> start_dist(0, num_of_points - 1);
    int start_v = start_dist(gen);
    std::vector<int> lens = {len1, len2, len3, len4};
    std::vector<std::vector<int>> parts(4);
    int cur = start_v;
    for (int i = 0; i < 4; ++i) {
      parts[i].reserve(lens[i]);
      for (int j = 0; j < lens[i]; ++j) {
        parts[i].push_back(cur);
        cur = ans.first[cur];
      }
    }
    std::vector<int> perm = {0, 1, 2, 3};
    std::shuffle(perm.begin(), perm.end(), gen);
    std::vector<int> mutated_path;
    mutated_path.reserve(num_of_points);
    for (int i = 0; i < 4; ++i) {
      int id = perm[i];
      for (size_t j = 0; j < parts[id].size(); ++j) {
        mutated_path.push_back(parts[id][j]);
      }
    }
    LinKernigan(mutated_path);
    ans.first.assign(num_of_points, -1);
    for (int i = 0; i < num_of_points; ++i) {
      ans.first[mutated_path[i]] = mutated_path[(i + 1) % num_of_points];
    }
    ans.second = FindDist(mutated_path);
    if (ans.second < best_known.second) {
      best_known.first = mutated_path;
      best_known.second = ans.second;
    }
  }

  void GeneticsWithMemetics() {
    int iters = 0;
    if (num_of_points > 500) {
      return;
    }
    GenPopulation();
    std::random_device rd;
    std::mt19937 gen(rd());
    std::uniform_real_distribution<double> prob_dist(0.0, 1.0);
    auto start = std::chrono::steady_clock::now();
    while (!Converged()) {
      auto end = std::chrono::steady_clock::now();
      auto duration = std::chrono::duration_cast<std::chrono::seconds>(end - start);
      if (duration.count() > 300) {
        break;
      }
      ++iters;
      if (iters % time_to_change == 0) {
        if (mut_prob - change >= min_mut_prob) {
          mut_prob -= change;
        }
      }
      /*if (iters % 100 == 0) {
        std::cout << std::fixed << std::setprecision(2);
        std::cout << "iters done: " << iters << " " << best_known.second << "\n"; 
      }*/
      std::vector<Ans> children;
      children.reserve(crossovers_num);
      std::uniform_int_distribution<int> parent_dist(0, static_cast<int>(population.size()) - 1);
      for (int i = 0; i < crossovers_num; ++i) {
        int p1 = parent_dist(gen);
        int p2 = parent_dist(gen);
        while (p2 == p1) {
          p2 = parent_dist(gen);
        }
        Ans child = DPX(p1, p2);
        if (prob_dist(gen) < mut_prob) {
          Mutation(child);
        }
        children.push_back(child);
      }
      std::vector<SPair> worst;
      worst.reserve(population.size());
      for (size_t i = 0; i < population.size(); ++i) {
        worst.push_back(SPair(population[i].second, static_cast<int>(i)));
      }
      std::sort(worst.begin(), worst.end(), Comp2);
      int replace_cnt = std::min(static_cast<int>(children.size()), static_cast<int>(population.size()));
      for (int i = 0; i < replace_cnt; ++i) {
        population[worst[i].second] = children[i];
      }
    }
  }

  Ans AnnealingStep() {
    std::random_device rd;
    std::mt19937 gen(rd());
    std::uniform_int_distribution<int> split_two(2, num_of_points - 2);
    int sum_part1 = split_two(gen);
    int sum_part2 = num_of_points - sum_part1;
    std::uniform_int_distribution<int> split_12(1, sum_part1 - 1);
    int len1 = split_12(gen);
    int len2 = sum_part1 - len1;
    std::uniform_int_distribution<int> split_34(1, sum_part2 - 1);
    int len3 = split_34(gen);
    int len4 = sum_part2 - len3;
    int lens[4] = {len1, len2, len3, len4};
    int pref[4] = {0, len1, len1 + len2, len1 + len2 + len3};
    std::uniform_int_distribution<int> start_dist(0, num_of_points - 1);
    int start_pos = start_dist(gen);
    std::vector<int> perm = {0, 1, 2, 3};
    std::shuffle(perm.begin(), perm.end(), gen);
    Ans n_path;
    const std::vector<int>& base = annelcur.first;
    n_path.first.reserve(num_of_points);
    for (int k = 0; k < 4; ++k) {
      int part_id = perm[k];
      int begin = (start_pos + pref[part_id]) % num_of_points;
      for (int j = 0; j < lens[part_id]; ++j) {
        n_path.first.push_back(base[(begin + j) % num_of_points]);
      }
    }
    LinKerniganFast(n_path.first);
    n_path.second = FindDist(n_path.first);
    return n_path;
  }

  void SetTemperature() {
    temp = 1E5;
    temp_change = 0.995;
    temp_stop = 1E-4;
    if (num_of_points > 500) {
      temp_change = 0.995;
    }
  }

  bool LinKerniganFast(std::vector<int>& path) {
    std::vector<VecPair> cycle(num_of_points);
    for (int i = 0; i < num_of_points; ++i) {
      int cur = path[i];
      int prev = path[(i - 1 + num_of_points) % num_of_points];
      int next = path[(i + 1) % num_of_points];
      cycle[cur] = VecPair(prev, next);
    }
    bool had_changes = false;
    bool round_improved = false;
    std::random_device rd;
    std::mt19937 gen(rd());
    std::uniform_int_distribution<int> start_dist(0, 2 * num_of_points - 1);
    auto start = std::chrono::steady_clock::now();
    do {
      auto end = std::chrono::steady_clock::now();
      auto duration = std::chrono::duration_cast<std::chrono::seconds>(end - start);
      if (duration.count() > 120) {
        break;
      }
      round_improved = false;
      for (int start = 0; start < FastLinKerniganIter; ++start) {
        int rand_start = start_dist(gen);
        int v = path[rand_start / 2];
        int w = (rand_start % 2 == 0 ? cycle[v].first : cycle[v].second);
        std::stack<std::pair<int, VecPair>> changes;
        db total_delta = 0;
        for (int iter = 0; iter < LinKerniganMaxSearch; ++iter) {
          int new_w = -1;
          int new_from = -1;
          db best_delta = 0;
          bool has_candidate = false;
          int prev_w = v;
          int cur_w = w;
          int max_steps = std::min(LinKerniganMaxNeib, num_of_points);
          for (int i = 0; i < max_steps; ++i) {
            int fut_w = cycle[cur_w].second;
            if (fut_w == prev_w) {
              fut_w = cycle[cur_w].first;
            }
            if (fut_w == v) {
              break;
            }
            db len_delta = Dist(v, cur_w) - Dist(v, w) - Dist(fut_w, cur_w) +
                           Dist(fut_w, w);
            if (i > 0 && (!has_candidate || len_delta < best_delta)) {
              best_delta = len_delta;
              new_w = cur_w;
              new_from = prev_w;
              has_candidate = true;
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
          if (new_w == -1) {
            break;
          }
          int fut_w = cycle[new_w].second;
          if (fut_w == new_from) {
            fut_w = cycle[new_w].first;
          }
          if (fut_w == v) {
            break;
          }
          total_delta += Dist(v, new_w) - Dist(v, w) - Dist(fut_w, new_w) +
                         Dist(fut_w, w);
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
          if (total_delta < -cEps) {
            break;
          }
        }
        if (total_delta >= -cEps) {
          while (!changes.empty()) {
            cycle[changes.top().first] = changes.top().second;
            changes.pop();
          }
          continue;
        }
        if (!changes.empty()) {
          had_changes = true;
          round_improved = true;
        }
      }
    } while (round_improved);
    if (!had_changes) {
      return false;
    }
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

  void Annealing() {
    SetTemperature();
    annelcur = best_known;
    std::random_device rd;
    std::mt19937 gen(rd());
    std::uniform_real_distribution<long double> prob(0.0L, 1.0L);
    int iters = 0;
    std::queue<long double> delta_queue;
    long double delta_sum = 0;
    while (temp > temp_stop) {
      ++iters;
      Ans cand = AnnealingStep();
      long double delta = cand.second - annelcur.second;
      delta_queue.push(delta);
      delta_sum += delta;
      if (delta_queue.size() > 20) {
        delta_sum -= delta_queue.front();
        delta_queue.pop();
      }
      if (delta < 0) {
        std::swap(annelcur, cand);
        MakeBetter(annelcur);
      } else {
        long double accept_prob = std::exp(-delta / temp);
        if (prob(gen) < accept_prob) {
          std::swap(annelcur, cand);
          MakeBetter(annelcur);
        }
      }
      temp *= temp_change;
      /*if (iters % 10000 == 20) {
        std::cout << std::setprecision(5);
        long double delta_avg = delta_sum / delta_queue.size();
        std::cout << "Temp par: " << iters << " " << temp << " " << delta_avg << " "
                  << -delta_avg / temp << " " << std::exp(-delta_avg / temp) << "\n";
      }*/
    }
    std::cout << "Final iters: " << iters << "\n";
  }

  bool NextPerm(std::vector<int>& perm) {
    int index = perm.size() - 1;
    while ((index > 0) && (perm[index] < perm[index - 1])) {
      --index;
    }
    std::reverse(perm.begin() + index, perm.end());
    if (index == 0) {
      return false;
    }
    int left = index;
    int right = perm.size();
    while (left < right - 1) {
      int mid = (left + right - 1) / 2;
      if (perm[mid] < perm[index - 1]) {
        left = mid + 1;
      } else {
        right = mid + 1;
      }
    }
    std::swap(perm[index - 1], perm[left]);
    return true;
  }

  db DistPop(int num1, int num2) {
    return Dist(popcur.first[num1], popcur.first[num2]);
  }

  db FindPermDist(int i, std::vector<int>& perm) {
    db ans = DistPop((num_of_points + i - 1) % num_of_points,
                  (i + perm[0]) % num_of_points);
    ans += DistPop((i + perm[perm.size() - 1]) % num_of_points,
                (i + int(perm.size())) % num_of_points);
    for (size_t j = 0; j < perm.size() - 1; ++j) {
      ans += DistPop((i + perm[j]) % num_of_points, (i + perm[j + 1]) % num_of_points);
    }
    return ans;
  }

  void SmallWindowPopMusic(int w_size = small_window_size) {
    std::vector<int> perm;
    perm.reserve(w_size);
    for (int i = 0; i < w_size; ++i) {
      perm.push_back(i);
    }
    int pos = 0;
    int start = 0;
    for (int i = 0; i < num_of_points; ++i) {
      std::vector<int> best_perm = perm;
      db best_dist = FindPermDist(pos, perm);
      bool changed = false;
      do {
        db dist = FindPermDist(pos, perm);
        if (dist < best_dist - cEps) {
          best_perm = perm;
          best_dist = dist;
          changed = true;
        }
      } while (NextPerm(perm));
      if (changed) {
        std::vector<int> copy;
        for (int j = 0; j < perm.size(); ++j) {
          copy.push_back(popcur.first[(pos + j) % num_of_points]);
        }
        for (int j = 0; j < perm.size(); ++j) {
          popcur.first[(pos + j) % num_of_points] = copy[best_perm[j]];
        }
      }
      pos += w_size / 2;
      if (pos > num_of_points - 1) {
        pos = ++start;
      }
    }
    popcur.second = FindDist(popcur.first);
  }

  void GreedyPopMusic(int w_size = greedy_window_size) {
    if (w_size > num_of_points - 1) {
      w_size = num_of_points - 1;
    }
    for (int start = 0; start < num_of_points; start += (w_size / 2)) {
      std::set<int> vert;
      std::vector<int> change;
      for (int i = 1; i <= w_size; ++i) {
        vert.insert((start + i) % num_of_points);
      }
      int curver = start;
      for (int i = 0; i < w_size; ++i) {
        int closest = -1;
        db less_dist = cInfty;
        for (auto iter = vert.begin(); iter != vert.end(); ++iter) {
          db dist = DistPop(curver, *iter);
          if (dist < less_dist) {
            closest = *iter;
            less_dist = dist;
          }
        }
        if (closest == -1) {
          throw std::runtime_error("Too small cInfty\n");
        }
        vert.erase(closest);
        change.push_back(closest);
        curver = closest;
      }
      db dist_before = DistPop(start, (start + 1) % num_of_points);
      dist_before += DistPop((start + w_size) % num_of_points,
                             (start + w_size + 1) % num_of_points);
      db dist_after = DistPop(start, change[0]);
      dist_after += DistPop(change[w_size - 1] % num_of_points,
                            (start + w_size + 1) % num_of_points);
      for (int i = 0; i < w_size - 1; ++i) {
        dist_before += DistPop((start + i + 1) % num_of_points,
                               (start + i + 2) % num_of_points);
        dist_after += DistPop(change[i], change[i + 1]);
      }
      if (dist_after < dist_before - cEps) {
        for (int i = 1; i <= w_size; ++i) {
          popcur.first[(start + i) % num_of_points] = change[i - 1];
        }
      }
    }
  }

  bool TwoOptPopMusic(std::vector<int>& window, int two_size) {
    bool changed = false;
    while (true) {
      int best_left = -1;
      int best_right = -1;
      db best_delta = -cEps;
      for (int left = 0; left + 2 < two_size; ++left) {
        for (int right = left + 2; right + 1 < two_size; ++right) {
          db delta = Dist(window[left], window[right]) +
                     Dist(window[left + 1], window[right + 1]) -
                     Dist(window[left], window[left + 1]) -
                     Dist(window[right], window[right + 1]);
          if (delta < best_delta) {
            best_delta = delta;
            best_left = left;
            best_right = right;
          }
        }
      }
      if (best_left == -1) {
        break;
      }
      std::reverse(window.begin() + best_left + 1, window.begin() + best_right + 1);
      changed = true;
    }
    return changed;
  }

  bool ThreeOptPopMusic(std::vector<int>& window, int three_size) {
    int window_size = static_cast<int>(window.size());
    int shift = three_size / 2;
    bool changed = false;
    for (int start = 0; start + three_size <= window_size; ) {
      while (true) {
        int best_left = -1;
        int best_mid = -1;
        int best_right = -1;
        int finish = start + three_size;
        for (int left = start; left + 5 < finish; ++left) {
          db best_delta = -cEps;
          for (int mid = left + 2; mid + 3 < finish; ++mid) {
            for (int right = mid + 2; right + 1 < finish; ++right) {
              int a = window[left];
              int b = window[left + 1];
              int c = window[mid];
              int d = window[mid + 1];
              int e = window[right];
              int f = window[right + 1];
              db delta = Dist(a, c) + Dist(b, e) + Dist(d, f) -
                         Dist(a, b) - Dist(c, d) - Dist(e, f);
              if (delta < best_delta) {
                best_delta = delta;
                best_left = left;
                best_mid = mid;
                best_right = right;
              }
            }
          }
          if (best_left == left) {
            break;
          }
        }
        if (best_left == -1) {
          break;
        }
        std::reverse(window.begin() + best_left + 1, window.begin() + best_mid + 1);
        std::reverse(window.begin() + best_mid + 1, window.begin() + best_right + 1);
        changed = true;
      }
      if (start + three_size == window_size) {
        break;
      }
      start += shift;
      if (start + three_size > window_size) {
        start = window_size - three_size;
      }
    }
    return changed;
  }

  void KOptPopMusic(int two_size = two_opt_window_size, int three_size = three_opt_window_size) {
    if (two_size > num_of_points) {
      two_size = num_of_points;
    }
    if (three_size > two_size) {
      three_size = two_size;
    }
    int shift = two_size / 2;
    for (int start = 0; start < num_of_points; start += shift) {
      std::vector<int> window;
      window.reserve(two_size);
      for (int i = 0; i < two_size; ++i) {
        window.push_back(popcur.first[(start + i) % num_of_points]);
      }
      TwoOptPopMusic(window, two_size);
      ThreeOptPopMusic(window, three_size);
      TwoOptPopMusic(window, two_size);
      ThreeOptPopMusic(window, three_size);
      /*int iter = 0;
      while (true) {
        ++iter;
        bool first = TwoOptPopMusic(window, two_size);
        bool second = ThreeOptPopMusic(window, three_size);
        if (!first && !second) {
          break;
        }
      }
      if (iter > 8) {
        std::cout << "iter is: " << iter << std::endl;
      }*/
      for (int i = 0; i < two_size; ++i) {
        popcur.first[(start + i) % num_of_points] = window[i];
      }
    }
    popcur.second = FindDist(popcur.first);
  }

  void MakeGreedyOrder(std::vector<VecPair>& new_vert, Ans& answ,
                       int start = 0) {
    int n_n_of_ver = static_cast<int>(new_vert.size());
    std::set<int> unused;
    for (int i = 0; i < n_n_of_ver; ++i) {
      if (i != start) {
        unused.insert(i);
      }
    }
    Ans cur;
    cur.first.reserve(size_t(n_n_of_ver));
    cur.first.push_back(start);
    int last = start;
    while (!unused.empty()) {
      int best_id = -1;
      db best_dist = cInfty;
      for (auto it = unused.begin(); it != unused.end(); ++it) {
        db dist = Dist(new_vert[size_t(last)].second,
                       new_vert[size_t(*it)].first);
        if (dist < best_dist) {
          best_dist = dist;
          best_id = *it;
        }
      }
      cur.first.push_back(best_id);
      unused.erase(best_id);
      last = best_id;
    }
    cur.second = 0;
    for (int i = 0; i < n_n_of_ver; ++i) {
      int from = cur.first[size_t(i)];
      int to = cur.first[size_t((i + 1) % n_n_of_ver)];
      cur.second += Dist(new_vert[size_t(from)].second,
                         new_vert[size_t(to)].first);
    }
    if (answ.first.empty() || cur.second < answ.second) {
      answ = cur;
    }
  }

  db AsymTwoOptBen(std::vector<VecPair>& new_vert, Ans& cur_answ, int first,
                   int second) {
    int n_n_of_ver = static_cast<int>(cur_answ.first.size());
    int first_next = (first + 1) % n_n_of_ver;
    int second_next = (second + 1) % n_n_of_ver;
    if (first == second || first_next == second || second_next == first) {
      return 0;
    }
    std::vector<int>& path = cur_answ.first;
    db ans = 0;
    ans -= Dist(new_vert[size_t(path[size_t(first)])].second,
                new_vert[size_t(path[size_t(first_next)])].first);
    ans -= Dist(new_vert[size_t(path[size_t(second)])].second,
                new_vert[size_t(path[size_t(second_next)])].first);
    ans += Dist(new_vert[size_t(path[size_t(first)])].second,
                new_vert[size_t(path[size_t(second)])].first);
    ans += Dist(new_vert[size_t(path[size_t(first_next)])].second,
                new_vert[size_t(path[size_t(second_next)])].first);
    int cur = first_next;
    while (cur != second) {
      int nxt = (cur + 1) % n_n_of_ver;
      ans -= Dist(new_vert[size_t(path[size_t(cur)])].second,
                  new_vert[size_t(path[size_t(nxt)])].first);
      ans += Dist(new_vert[size_t(path[size_t(nxt)])].second,
                  new_vert[size_t(path[size_t(cur)])].first);
      cur = nxt;
    }
    return ans;
  }

  void AsymTwoOpt(std::vector<VecPair>& new_vert, Ans& cur_answ, int first,
                  int second) {
    int n_n_of_ver = static_cast<int>(cur_answ.first.size());
    int first_next = (first + 1) % n_n_of_ver;
    int second_next = (second + 1) % n_n_of_ver;
    if (first == second || first_next == second || second_next == first) {
      return;
    }
    cur_answ.second += AsymTwoOptBen(new_vert, cur_answ, first, second);
    int len = 1;
    int cur = first_next;
    while (cur != second) {
      ++len;
      cur = (cur + 1) % n_n_of_ver;
    }
    for (int i = 0; i < len / 2; ++i) {
      std::swap(cur_answ.first[size_t((first_next + i) % n_n_of_ver)],
                cur_answ.first[size_t((first_next + len - 1 - i) % n_n_of_ver)]);
    }
  }

  void AsymetricMakeBetter(Ans& answ, Ans& answ_cur) {
    if (answ_cur.second < answ.second) {
      answ = answ_cur;
    }
  }

  void PopSetTemperature() {
    ptemp = 1E5;
    ptemp_change = 0.995;
    ptemp_stop = 1E-4;
  }

  void AsymTwoOptMaxIter(std::vector<VecPair>& new_vert, Ans& answ,
                         int n_n_of_ver) {
    int begin = 0;
    while(true) {
      bool changed = false;
      for (int i = 0; i < n_n_of_ver; ++i) {
        for (int j = 1; j < n_n_of_ver; ++j) {
          int v_first = (begin) % n_n_of_ver;
          int v_second = (begin + j) % n_n_of_ver;
          if (AsymTwoOptBen(new_vert, answ, v_first, v_second) < -cEps) {
            AsymTwoOpt(new_vert, answ, v_first, v_second);
            changed = true;
          }
          if (changed) {
            break;
          }
        }
        if (changed) {
          break;
        }
        ++begin;
        if (begin >= n_n_of_ver) {
          begin %= n_n_of_ver;
        }
      }
      if (!changed) {
        break;
      }
    }
  }

  void AsymAnelTwoOpt(std::vector<VecPair>& new_vert, Ans& n_path) {
    int n_n_of_ver = static_cast<int>(n_path.first.size());
    int begin = 0;
    while(true) {
      bool changed = false;
      for (int i = 0; i < n_n_of_ver; ++i) {
        for (int j = 1; j < n_n_of_ver; ++j) {
          int v_first = (begin) % n_n_of_ver;
          int v_second = (begin + j) % n_n_of_ver;
          if (AsymTwoOptBen(new_vert, n_path, v_first, v_second) < -cEps) {
            AsymTwoOpt(new_vert, n_path, v_first, v_second);
            changed = true;
          }
          if (changed) {
            break;
          }
        }
        if (changed) {
          break;
        }
        ++begin;
        if (begin >= n_n_of_ver) {
          begin %= n_n_of_ver;
        }
      }
      if (!changed) {
        break;
      }
    }
  }

  Ans AsymAnnealingStep(std::vector<VecPair>& new_vert, Ans& cur_answ) {
    int n_n_of_ver = static_cast<int>(cur_answ.first.size());
    if (n_n_of_ver < 4) {
      return cur_answ;
    }
    std::random_device rd;
    std::mt19937 gen(rd());
    std::uniform_int_distribution<int> split_two(2, n_n_of_ver - 2);
    int sum_part1 = split_two(gen);
    int sum_part2 = n_n_of_ver - sum_part1;
    std::uniform_int_distribution<int> split_12(1, sum_part1 - 1);
    int len1 = split_12(gen);
    int len2 = sum_part1 - len1;
    std::uniform_int_distribution<int> split_34(1, sum_part2 - 1);
    int len3 = split_34(gen);
    int len4 = sum_part2 - len3;
    int lens[4] = {len1, len2, len3, len4};
    int pref[4] = {0, len1, len1 + len2, len1 + len2 + len3};
    std::uniform_int_distribution<int> start_dist(0, n_n_of_ver - 1);
    int start_pos = start_dist(gen);
    std::vector<int> perm = {0, 1, 2, 3};
    std::shuffle(perm.begin(), perm.end(), gen);
    Ans n_path;
    const std::vector<int>& base = cur_answ.first;
    n_path.first.reserve(size_t(n_n_of_ver));
    for (int k = 0; k < 4; ++k) {
      int part_id = perm[k];
      int begin = (start_pos + pref[part_id]) % n_n_of_ver;
      for (int j = 0; j < lens[part_id]; ++j) {
        n_path.first.push_back(base[size_t((begin + j) % n_n_of_ver)]);
      }
    }
    n_path.second = 0;
    for (int i = 0; i < n_n_of_ver; ++i) {
      int from = n_path.first[size_t(i)];
      int to = n_path.first[size_t((i + 1) % n_n_of_ver)];
      n_path.second += Dist(new_vert[size_t(from)].second,
                            new_vert[size_t(to)].first);
    }
    AsymAnelTwoOpt(new_vert, n_path);
    n_path.second = 0;
    for (int i = 0; i < n_n_of_ver; ++i) {
      int from = n_path.first[size_t(i)];
      int to = n_path.first[size_t((i + 1) % n_n_of_ver)];
      n_path.second += Dist(new_vert[size_t(from)].second,
                            new_vert[size_t(to)].first);
    }
    return n_path;
  }

  void AsymetricAnnealing(std::vector<VecPair>& new_vert, Ans& answ,
                          int n_n_of_ver) {
    PopSetTemperature();
    Ans answ_cur = answ;
    std::random_device rd;
    std::mt19937 gen(rd());
    std::uniform_real_distribution<long double> prob(0.0L, 1.0L);
    std::uniform_int_distribution<int> distrib(0, n_n_of_ver - 1);
    int iters = 0;
    while (ptemp > ptemp_stop) {
      ++iters;
      std::cout << iters << " ";
      if (iters % 100 == 0) {
        std::cout << std::endl;
      }
      /*int first = distrib(gen);
      int second = distrib(gen);*/
      Ans cand = AsymAnnealingStep(new_vert, answ_cur);
      //db delta = AsymTwoOptBen(new_vert, answ_cur, first, second);
      db delta = cand.second - answ_cur.second;
      if (delta < 0) {
        //AsymTwoOpt(new_vert, answ_cur, first, second);
        std::swap(answ_cur, cand);
        AsymetricMakeBetter(answ, answ_cur);
      } else {
        long double accept_prob = std::exp(-delta / ptemp);
        if (prob(gen) < accept_prob) {
          //AsymTwoOpt(new_vert, answ_cur, first, second);
          std::swap(answ_cur, cand);
          AsymetricMakeBetter(answ, answ_cur);
        }
      }
      ptemp *= ptemp_change;
    }
    AsymTwoOptMaxIter(new_vert, answ_cur, n_n_of_ver);
    AsymetricMakeBetter(answ, answ_cur);
    std::cout << "Final iters: " << iters << "\n";
  }

  std::vector<int> SolveAsymetricTsp(std::vector<VecPair>& new_vert) {
    Ans answ;
    int n_n_of_ver = static_cast<int>(new_vert.size());
    answ.first.reserve(size_t(n_n_of_ver));
    for (int i = 0; i < n_n_of_ver; ++i) {
      answ.first.push_back(i);
    }
    answ.second = 0;
    for (int i = 0; i < n_n_of_ver; ++i) {
      int from = answ.first[size_t(i)];
      int to = answ.first[size_t((i + 1) % n_n_of_ver)];
      answ.second += Dist(new_vert[size_t(from)].second,
                          new_vert[size_t(to)].first);
    }
    for (int i = 0; i < n_n_of_ver; ++i) {
      MakeGreedyOrder(new_vert, answ, i);
    }
    AsymTwoOptMaxIter(new_vert, answ, n_n_of_ver);
    /*for (int i = 0; i < pop_annealing_retry; ++i) {
      AsymetricAnnealing(new_vert, answ, n_n_of_ver);
    }*/
    return answ.first;
  }

  void PopBreakAndBuild() {
    std::vector<SPair> dists;
    dists.reserve(num_of_points);
    for (int i = 0; i < num_of_points; ++i) {
      dists.push_back(SPair(Dist(popcur.first[i],
                                 popcur.first[(i + 1) % num_of_points]), i));
    }
    std::sort(dists.begin(), dists.end(), Comp2);
    std::vector<int> remedges;
    int n_n_of_ver = std::min(num_of_points,
        std::max(int(double(num_of_points) * destroy), pop_rebuild_min_num));
    remedges.reserve(size_t(n_n_of_ver));
    for (int i = 0; i < size_t(n_n_of_ver); ++i) {
      remedges.push_back(dists[i].second);
    }
    std::sort(remedges.begin(), remedges.end());
    std::vector<int> old_path = popcur.first;
    std::vector<VecPair> new_vert;
    new_vert.resize(size_t(n_n_of_ver));
    std::vector<int> part_begin;
    std::vector<int> part_end;
    part_begin.resize(size_t(n_n_of_ver));
    part_end.resize(size_t(n_n_of_ver));
    for (int i = 0; i < n_n_of_ver; ++i) {
      part_begin[size_t((i + 1) % n_n_of_ver)] = (remedges[i] + 1) % num_of_points;
      part_end[size_t(i)] = remedges[i];
    }
    for (int i = 0; i < n_n_of_ver; ++i) {
      new_vert[size_t(i)].first = old_path[size_t(part_begin[size_t(i)])];
      new_vert[size_t(i)].second = old_path[size_t(part_end[size_t(i)])];
    }
    std::vector<int> sol = SolveAsymetricTsp(new_vert);
    std::vector<int> new_path;
    new_path.reserve(num_of_points);
    for (int i = 0; i < n_n_of_ver; ++i) {
      int part_id = sol[i];
      int cur = part_begin[size_t(part_id)];
      while (true) {
        new_path.push_back(old_path[size_t(cur)]);
        if (cur == part_end[size_t(part_id)]) {
          break;
        }
        cur = (cur + 1) % num_of_points;
      }
    }
    popcur.first.swap(new_path);
    popcur.second = FindDist(popcur.first);
  }

  void PopMakeBetter(Ans& other) {
    if (other.second < best_known.second) {
      best_known = other;
    }
  }

  void PopMusic() {
    std::cout << std::fixed << std::setprecision(2);
    popcur = best_known;
    db value = popcur.second;
    if (num_of_points > 2000) {
      KOptPopMusic(200, 50);
      std::cout << "Done; " << popcur.second << std::endl;
      KOptPopMusic(1000, 150);
      std::cout << "Done; " << popcur.second << std::endl;
    }
    while(true) {
      //SmallWindowPopMusic();
      //GreedyPopMusic();
      KOptPopMusic();
      PopMakeBetter(popcur);
      std::cout << "Done; " << popcur.second << std::endl;
      if (popcur.second > value - cEps) {
        PopBreakAndBuild();
        std::cout << "Rebuild is done, " << popcur.second << std::endl;
        KOptPopMusic();
        std::cout << "Done after rebuild; " << popcur.second << std::endl;
        if (popcur.second > value - cEps) {
          break;
        }
      }
      value = popcur.second;
    }
    MakeBetter(popcur);
  }

 public:

  int cMaxForSort = 1915; // Max time is 2 seconds, since x^2 log_2(x)
  int cNumOfneigh = 100;
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
      two_opt_iters = 1000;
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
    /*eur = TwoOptMaxIter(best_known);
    MakeBetter(eur);
    RunKernigan();
    GeneticsWithMemetics();
    Annealing();*/
    PopMusic();
    OutAns(out);
  }
};

/*int main() {
  std::ostringstream out;
  TSPSolver solve("data/tsp_51_1", out);
  std::cout << out.str();
}*/
