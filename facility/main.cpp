#include <algorithm>
#include <cassert>
#include <chrono>
#include <cmath>
#include <iomanip>
#include <iostream>
#include <fstream>
#include <map>
#include <queue>
#include <random>
#include <set>
#include <sstream>
#include <stdexcept>
#include <string>
#include <unordered_set>
#include <vector>
#include "coin/ClpSimplex.hpp"

struct FacilitySolver {
 private:
  struct Store;
  struct Guy;
  using db = long double;
  using Ans = std::pair<std::vector<bool>, db>;
  static inline const db cInfty = 1E10;
  static inline const db cEps = 1E-3;
  static inline const db cSimpEps = 1E-5;
  int shops;
  int people;
  int cClosestEurTimes = 1;
  int pop_size = 8;
  int child_size = 8;
  int safe_zone = 0;
  int corv_attempts = 20;
  int gen_time = 180;
  int mut_pos = 10;
  int num_of_clos = 10; // for clos_stores
  int time = 0;
  int tabu_ban = -1;
  int close_num = 5; // for people neighbourhood
  int pot_swaps = 3;
  int max_depth = 6;
  int global_retries = 20;
  int beam_const = 6;
  int lp_beam_const = 3;
  int lp_beam_sons = 1000;
  int lp_beam_max_tries = 5000;
  db beam_coef = 1;
  db temp = 10000;
  db temp_change = 0.9999;
  db temp_delta = 0.995;
  db temp_stop = 1E-8;
  db total_demand = 0;
  db first_demand = 0;
  db high_dif = 3;
  std::vector<Store> stores;
  std::vector<Guy> guys;
  std::vector<int> cur_ans;
  std::vector<int> best_ans;
  std::vector<std::vector<int>> guy_pref;
  std::vector<std::vector<int>> clos_store;
  std::vector<std::vector<int>> hamming_dist;
  std::vector<std::vector<bool>> population;
  std::vector<db> pop_values;
  std::vector<db> third_dist;
  std::map<std::pair<int, int>, int> tabu_list;
  std::set<int> store_open;
  std::vector<int> shufle;
  db cur_ans_val = cInfty;
  db best_ans_val = cInfty;
  db pop_prob = 0.75;
  db mut_prob = 0.20;
  db corv_alpha = 0.02;
  bool cur_ans_counted = false;

  static db Dist(const Store& st, const Guy& gu) {
    db x_sq = st.x - gu.x;
    db y_sq = st.y - gu.y;
    return std::sqrt(x_sq * x_sq + y_sq * y_sq);
  }

  static db Dist(const Guy& gu, const Store& st) {
    return Dist(st, gu);
  }

  static db Dist(const Store& first, const Store& second) {
    db x_sq = first.x - second.x;
    db y_sq = first.y - second.y;
    return std::sqrt(x_sq * x_sq + y_sq * y_sq);
  }

  struct Store {
    const db open;
    const db cap;
    const db x;
    const db y;
    db taken = 0;
    bool is_open = false;
    std::set<int> guys;

    Store() = default;

    Store(db op, db cp, db x, db y)
      : open(op)
      , cap(cp)
      , x(x)
      , y(y)
    {}

    bool is_good() {
      return taken <= cap;
    }

    bool can_take(db new_cap) {
      return taken + new_cap <= cap;
    }

    bool can_take(const Guy& new_guy) {
      return taken + new_guy.demand <= cap;
    }

    db add_cost(const Guy& new_guy) {
      if (!can_take(new_guy)) {
        return cInfty;
      }
      if (is_open) {
        return Dist(*this, new_guy);
      }
      return Dist(*this, new_guy) + open;
    }

    void Add(int index, const Guy& new_guy) {
      if (!can_take(new_guy)) {
        throw std::runtime_error("Adding when can't add");
      }
      is_open = true;
      guys.insert(index);
      taken += new_guy.demand;
    }

    db rem_cost(const Guy& new_guy) {
      if (guys.size() > 1) {
        return Dist(*this, new_guy);
      }
      return Dist(*this, new_guy) + open;
    }

    void Rem(int index, const Guy& new_guy) {
      if (guys.count(index) == 0) {
        throw std::runtime_error("Removing when no guy");
      }
      guys.erase(index);
      taken -= new_guy.demand;
      if (guys.empty()) {
        is_open = false;
      }
    }

    bool CanTwoOpt(const Guy& rem, const Guy& add) {
      return taken - rem.demand + add.demand <= cap;
    }

    db TwoOptBen(const Guy& rem, const Guy& add) {
      if (!CanTwoOpt(rem, add)) {
        return -cInfty;
      }
      return Dist(*this, rem) - Dist(*this, add);
    }

    void Clean() {
      taken = 0;
      is_open = false;
      guys.clear();
    }
  };

  struct Guy {
    const db demand;
    const db x;
    const db y;
    int go_to = -1;

    Guy() = default;

    Guy(db dem, db x, db y)
      : demand(dem)
      , x(x)
      , y(y)
    {}
  };

  void InputData(std::string& path) {
    std::ifstream input_file(path);
    input_file >> shops >> people;
    stores.reserve(shops);
    guys.reserve(people);
    for (int i = 0; i < shops; ++i) {
      db open, cap, x, y;
      input_file >> open >> cap >> x >> y;
      stores.push_back(Store(open, cap, x, y));
    }
    for (int i = 0; i < people; ++i) {
      db demand, x, y;
      input_file >> demand >> x >> y;
      guys.push_back(Guy(demand, x, y));
    }
  }

  bool CountCurAns() {
    cur_ans_val = cInfty;
    cur_ans_counted = false;
    db ans = 0;
    std::set<int> stores_open;
    for (int i = 0; i < people; ++i) {
      if (cur_ans[i] == -1) {
        return false;
      }
      stores_open.insert(cur_ans[i]);
      ans += Dist(stores[cur_ans[i]], guys[i]);
    }
    for (auto i: stores_open) {
      ans += stores[i].open;
    }
    cur_ans_counted = true;
    cur_ans_val = ans;
    return true;
  }

  void SetBetter() {
    if (!cur_ans_counted) {
      if (!CountCurAns()) {
        return;
      }
    }
    if (cur_ans_val < best_ans_val) {
      best_ans_val = cur_ans_val;
      best_ans = cur_ans;
    }
  }

  using SPair1 = std::pair<int, db>;

  static bool Comp1(SPair1 ft, SPair1 sc) {
    return ft.second < sc.second;
  }

  void SetGuyPreference() {
    for (int i = 0; i < people; ++i) {
      std::vector<SPair1> for_sort;
      for_sort.reserve(shops);
      for (int j = 0; j < shops; ++j) {
        for_sort.push_back({j, Dist(stores[j], guys[i])});
      }
      std::sort(for_sort.begin(), for_sort.end(), Comp1);
      guy_pref.push_back({});
      for (int j = 0; j < shops; ++j) {
        guy_pref.back().push_back(for_sort[j].first);
      }
    }
  }

  void CleanStores() {
    for (int i = 0; i < shops; ++i) {
      stores[i].Clean();
    }
  }

  db GetShafleEur(const std::vector<int>& shufle, std::vector<int>& where) {
    if (shufle.size() != people) {
      throw std::runtime_error("Given shufle is cringe");
    }
    CleanStores();
    if (where.size() != people) {
      where.resize(people);
    }
    db ans = 0;
    for (int i = 0; i < people; ++i) {
      bool found_shop = false;
      for (int j = 0; j < shops; ++j) {
        if (stores[guy_pref[shufle[i]][j]].can_take(guys[shufle[i]])) {
          found_shop = true;
          ans += stores[guy_pref[shufle[i]][j]].add_cost(guys[shufle[i]]);
          stores[guy_pref[shufle[i]][j]].Add(shufle[i], guys[shufle[i]]);
          where[shufle[i]] = guy_pref[shufle[i]][j];
          guys[shufle[i]].go_to = guy_pref[shufle[i]][j];
          break;
        }
      }
      if (!found_shop) {
        throw std::runtime_error("Did not found a greedy solution");
      }
    }
    return ans;
  }

  void ClosestEur() {
    std::random_device rd;
    std::mt19937 gen(rd());
    for (int i = 0; i < cClosestEurTimes; ++i) {
      std::shuffle(shufle.begin(), shufle.end(), gen);
      cur_ans_val = GetShafleEur(shufle, cur_ans);
      cur_ans_counted = true;
      SetBetter();
    }
  }

  void OutputData(std::ostringstream& out)  {
    out << std::fixed << std::setprecision(3);
    out << best_ans_val << "\n";
    for (int i = 0; i < people; ++i) {
      out << best_ans[i] << " ";
    }
    out << "\n";
  }

  void SetStoresAndGuys(const std::vector<int>& sol) {
    CleanStores();
    for (int i = 0; i < people; ++i) {
      guys[i].go_to = sol[i];
      stores[sol[i]].Add(i, guys[i]);
    }
  }

  int OneOpt() {
    int iter = 0;
    int ii = 0;
    while (true) {
      bool changed = false;
      for (int jj = 0; jj < people; ++jj) {
        int i = (ii + jj) % people;
        int best_var = guys[i].go_to;
        db ben = 0;
        for (int j = 0; j < shops; ++j) {
          if (j == guys[i].go_to) {
            continue;
          }
          db ben_other = stores[guys[i].go_to].rem_cost(guys[i]) -
                         stores[j].add_cost(guys[i]);
          if (ben_other > ben) {
            best_var = j;
            ben = ben_other;
          }
        }
        if (ben > 0) {
          changed = true;
          ii = i + 1;
          stores[guys[i].go_to].Rem(i, guys[i]);
          stores[best_var].Add(i, guys[i]);
          cur_ans_val -= ben;
          cur_ans[i] = best_var;
          if (cur_ans_val < 0) {
            throw std::logic_error("Cur_ans_val is impossible!");
          }
          guys[i].go_to = best_var;
          break;
        }
      }
      if (changed) {
        ++iter;
      } else {
        break;
      }
    }
    return iter;
  }

  int TwoOpt() {
    int iter = 0;
    while (true) {
      bool changed = false;
      for (int i = 0; i < people; ++i) {
        for (int j = i + 1; j < people; ++j) {
          if (cur_ans[i] == cur_ans[j]) {
            continue;
          }
          int sh_f = cur_ans[i];
          int sh_s = cur_ans[j];
          if (stores[sh_f].TwoOptBen(guys[i], guys[j]) +
              stores[sh_s].TwoOptBen(guys[j], guys[i]) > cEps) {
            changed = true;
            std::swap(cur_ans[i], cur_ans[j]);
            cur_ans_val -= stores[sh_f].TwoOptBen(guys[i], guys[j]) +
                           stores[sh_s].TwoOptBen(guys[j], guys[i]);
            if (cur_ans_val < 0) {
              throw std::logic_error("Cur_ans_val is impossible!");
            }
            stores[sh_f].Rem(i, guys[i]);
            stores[sh_s].Rem(j, guys[j]);
            stores[sh_s].Add(i, guys[i]);
            stores[sh_f].Add(j, guys[j]);
            guys[i].go_to = sh_s;
            guys[j].go_to = sh_f;
            break;
          }
        }
        if (changed) {
          break;
        }
      }
      if (changed) {
        ++iter;
      } else {
        break;
      }
    }
    return iter;
  }

  bool OneTwoOpt() {
    if (best_ans_val == cInfty) {
      throw std::runtime_error("Solution for OneTwoOpt is not initialized");
    }
    bool changed = false;
    changed = changed || (OneOpt() > 0);
    //std::cout << "Done iterations: " << OneOpt() << "\n";
    SetBetter();
    changed = changed || (TwoOpt() > 0);
    //std::cout << "Done TwoOpt iterations: " << TwoOpt() << "\n";
    SetBetter();
    return changed;
  }

  bool TryClosingStore(int store_num) {
    if (!stores[store_num].is_open) {
      return false;
    }
    std::vector<int> store_guys(stores[store_num].guys.begin(),
                                stores[store_num].guys.end());
    std::random_device rd;
    std::mt19937 gen(rd());
    std::shuffle(store_guys.begin(), store_guys.end(), gen);
    for (int guy_num : store_guys) {
      stores[store_num].Rem(guy_num, guys[guy_num]);
    }
    db delta = -stores[store_num].open;
    bool all_moved = true;
    for (int guy_num : store_guys) {
      int new_store = -1;
      for (int candidate : guy_pref[guy_num]) {
        if (candidate != store_num && stores[candidate].is_open &&
            stores[candidate].can_take(guys[guy_num])) {
          new_store = candidate;
          break;
        }
      }
      if (new_store == -1) {
        all_moved = false;
        break;
      }
      delta += Dist(stores[new_store], guys[guy_num]) -
               Dist(stores[store_num], guys[guy_num]);
      stores[new_store].Add(guy_num, guys[guy_num]);
      guys[guy_num].go_to = new_store;
      cur_ans[guy_num] = new_store;
    }
    if (all_moved && delta < -cEps) {
      cur_ans_val += delta;
      return true;
    }
    for (int guy_num : store_guys) {
      if (cur_ans[guy_num] != store_num) {
        stores[cur_ans[guy_num]].Rem(guy_num, guys[guy_num]);
      }
      stores[store_num].Add(guy_num, guys[guy_num]);
      guys[guy_num].go_to = store_num;
      cur_ans[guy_num] = store_num;
    }
    return false;
  }

  bool CloseUnnessesary() {
    bool changed = false;
    while(true) {
      bool improved = false;
      std::vector<SPair1> sorted;
      for (int i = 0; i < shops; ++i) {
        sorted.push_back({i, stores[i].cap - stores[i].taken});
      }
      std::sort(sorted.begin(), sorted.end(), Comp1);
      for (int i = shops - 1; i >= 0; --i) {
        improved = improved || TryClosingStore(sorted[i].first);
      }
      if (improved) {
        changed = true;
      }
      if (!improved) {
        break;
      }
    }
    CountCurAns();
    SetBetter();
    return changed;
  }

  void GeneralGreedy() {
    cur_ans = best_ans;
    CountCurAns();
    SetStoresAndGuys(cur_ans);
    while (true) {
      bool changed = false;
      changed = changed || OneTwoOpt();
      changed = changed || CloseUnnessesary();
      if (!changed) {
        break;
      }
    }
  }
  
  db MaskFitness(std::vector<bool>& mask, bool dont_improve = false) {
    CleanStores();
    cur_ans.assign(people, -1);
    cur_ans_val = 0;
    cur_ans_counted = false;
    for (int i = 0; i < people; ++i) {
      guys[i].go_to = -1;
    }
    std::random_device rd;
    std::mt19937 gen(rd());
    std::shuffle(shufle.begin(), shufle.end(), gen);
    for (int guy_num : shufle) {
      int store_num = -1;
      for (int candidate : guy_pref[guy_num]) {
        if (mask[candidate] && stores[candidate].can_take(guys[guy_num])) {
          store_num = candidate;
          break;
        }
      }
      if (store_num == -1) {
        cur_ans_val = cInfty;
        return cInfty;
      }
      cur_ans_val += stores[store_num].add_cost(guys[guy_num]);
      stores[store_num].Add(guy_num, guys[guy_num]);
      guys[guy_num].go_to = store_num;
      cur_ans[guy_num] = store_num;
    }
    cur_ans_counted = true;
    if (!dont_improve) {
      OneTwoOpt();
      CloseUnnessesary();
      OneTwoOpt();
    } else {
      CloseUnnessesary();
    }
    /*while (true) {
      bool changed = false;
      changed = changed || OneTwoOpt();
      changed = changed || CloseUnnessesary();
      if (!changed) {
        break;
      }
    }*/
    for (int i = 0; i < shops; ++i) {
      mask[i] = stores[i].is_open;
    }
    return cur_ans_val;
  }

  void GenPopulation() {
    auto start = std::chrono::steady_clock::now();
    std::vector<bool> best_mask(shops, false);
    for (size_t i = 0; i < best_ans.size(); ++i) {
      best_mask[best_ans[i]] = true;
    }
    population.clear();
    bool dont_improve = false;
    db val = MaskFitness(best_mask);
    population.push_back(best_mask);
    pop_values.push_back(val);
    for (int i = 1; i < pop_size; ++i) {
      auto end = std::chrono::steady_clock::now();
      auto duration = std::chrono::duration_cast<std::chrono::seconds>(end - start);
      if (duration.count() > 15) {
        dont_improve = true;
      }
      if (duration.count() > 45) {
        pop_size = i;
        break;
      }
      std::vector<bool> new_mask = best_mask;
      std::random_device rd;
      std::mt19937 gen(rd());
      std::uniform_real_distribution<long double> dis(0.0, 1.0);
      for (int j = 0; j < shops; ++j) {
        db value = dis(gen);
        if (value <= pop_prob) {
          new_mask[j] = !new_mask[j];
        }
      }
      db value = MaskFitness(new_mask, dont_improve);
      while (value > cInfty - cEps) {
        for (int j = 0; j < shops; ++j) {
          if (best_mask[j] && !new_mask[j]) {
            new_mask[j] = true;
          }
          if (new_mask[j]) {
            continue;
          }
          db value = dis(gen);
          if (value <= pop_prob) {
            new_mask[j] = !new_mask[j];
          }
        }
        value = MaskFitness(new_mask, dont_improve);
      }
      population.push_back(new_mask);
      pop_values.push_back(value);
    }
    //std::cout << "Total pop_size = " << pop_size << "\n";
  }

  void FindHammingDist() {
    hamming_dist.assign(pop_size, std::vector<int>(pop_size, 0));
    for (int i = 0; i < pop_size; ++i) {
      for (int j = 0; j < pop_size; ++j) {
        for (int k = 0; k < shops; ++k) {
          if (population[i][k] != population[j][k]) {
            ++hamming_dist[i][j];
          }
        }
      }
    }
    static std::ofstream output_file("ham_dist.txt");
    for (int i = 0; i < pop_size; ++i) {
      for (int j = 0; j < pop_size; ++j) {
        output_file << std::setw(3) << hamming_dist[i][j] << ", ";
      }
      output_file << "\n";
    }
    output_file << "#############################" << shops << "#####################" << std::endl;
  }

  Ans DPX(int first, int second) {
    Ans ans;
    ans.first.resize(shops, false);
    std::vector<int> mismatch;
    for (int i = 0; i < shops; ++i) {
      if (population[first][i] && population[second][i]) {
        ans.first[i] = true;
        continue;
      }
      if (population[first][i] || population[second][i]) {
        mismatch.push_back(i);
      }
    }
    std::random_device rd;
    std::mt19937 gen(rd());
    std::uniform_real_distribution<long double> dis(0.0, 1.0);
    while (MaskFitness(ans.first) > cInfty - cEps) {
      if (mismatch.empty()) {
        for (int i = 0; i < shops; ++i) {
          if (population[first][i] || population[second][i]) {
            ans.first[i] = true;
          }
        }
        ans.second = MaskFitness(ans.first);
        return ans;
      }
      for (int i = 0; i < mismatch.size(); ++i) {
        db value = dis(gen);
        if (value <= 0.5) {
          ans.first[mismatch[i]] = true;
          mismatch[i] = -1;
        }
      }
      std::vector<int> mismatch_swap;
      for (int i = 0; i < mismatch.size(); ++i) {
        if (mismatch[i] != -1) {
          mismatch_swap.push_back(mismatch[i]);
        }
      }
      std::swap(mismatch, mismatch_swap);
    }
    ans.second = cur_ans_val;
    return ans;
  }

  void Compete(std::set<int>& pass, std::vector<SPair1>& best_values, std::vector<int>& not_pass) {
    std::vector<int> left_ind;
    for (int i = safe_zone; i < pop_size + child_size; ++i) {
      left_ind.push_back(i);
    }
    std::random_device rd;
    std::mt19937 gen(rd());
    while (static_cast<int>(left_ind.size()) > pop_size - safe_zone) {
      std::uniform_int_distribution<int> dis(0, static_cast<int>(left_ind.size()) - 1);
      int first = dis(gen);
      int second = dis(gen);
      while (first  == second) {
        second = dis(gen);
      }
      if (best_values[left_ind[first]].second < best_values[left_ind[second]].second) {
        if (best_values[left_ind[second]].first < pop_size) {
          not_pass.push_back(best_values[left_ind[second]].first);
        }
        std::swap(left_ind[second], left_ind[left_ind.size() - 1]);
        left_ind.pop_back();
      } else {
        if (best_values[left_ind[first]].first < pop_size) {
          not_pass.push_back(best_values[left_ind[first]].first);
        }
        std::swap(left_ind[first], left_ind[left_ind.size() - 1]);
        left_ind.pop_back();
      }
    }
    for (int i = 0; i < left_ind.size(); ++i) {
      pass.insert(best_values[left_ind[i]].first);
    }
  }

  bool Converged() {
    std::random_device rd;
    std::mt19937 gen(rd());
    std::uniform_int_distribution<int> dis(0, pop_size - 1);
    db average = 0;
    for (int i = 0; i < corv_attempts; ++i) {
      int first = dis(gen);
      int second = dis(gen);
      while (first == second) {
        second = dis(gen);
      }
      for (int j = 0; j < shops; ++j) {
        if (population[first][j] != population[second][j]) {
          average += 1;
        }
      }
    }
    average /= corv_attempts;
    if (average < corv_alpha * shops) {
      //std::cout << "Reason to break is: " << average << "\n";
    }
    return average < corv_alpha * shops;
  }

  void Mutation(int pos) {
    std::random_device rd;
    std::mt19937 gen(rd());
    std::uniform_int_distribution<int> dis(0, shops - 1);
    for (int i = 0; i < mut_pos; ++i) {
      int bit = dis(gen);
      while (population[pos][bit]) {
        bit = dis(gen);
      }
      population[pos][bit] = true;
    }
    pop_values[pos] = MaskFitness(population[pos]);
  }

  void Genetics() {
    static std::ofstream output_file("iter.txt");
    output_file << std::fixed << std::setprecision(2);
    GenPopulation();
    auto start = std::chrono::steady_clock::now();
    int iterations = 0;
    while (true) {
      //FindHammingDist();
      if (Converged()) {
        break;
      }
      auto end = std::chrono::steady_clock::now();
      auto duration = std::chrono::duration_cast<std::chrono::seconds>(end - start);
      if (duration.count() > gen_time) {
        break;
      }
      ++iterations;
      std::vector<Ans> childs;
      std::random_device rd;
      std::mt19937 gen(rd());
      std::uniform_int_distribution<int> dis(0, pop_size - 1);
      for (int i = 0; i < child_size; ++i) {
        int first = dis(gen);
        int second = dis(gen);
        while (second == first) {
          second = dis(gen);
        }
        childs.push_back(DPX(first, second));
      }
      std::vector<SPair1> best_values;
      for (int i = 0; i < pop_size + child_size; ++i) {
        if (i < pop_size) {
          best_values.push_back(SPair1(i, pop_values[i]));
        } else {
          best_values.push_back(SPair1(i, childs[i - pop_size].second));
        }
      }
      std::sort(best_values.begin(), best_values.end(), Comp1);
      output_file << "On iteration " << iterations << " best metric is: " << best_values[0].second << std::endl;
      std::set<int> pass;
      std::vector<int> not_pass;
      for (int i = 0; i < safe_zone; ++i) {
        pass.insert(best_values[i].first);
      }
      Compete(pass, best_values, not_pass);
      for (int index : pass) {
        if (index >= pop_size) {
          int place = not_pass.back();
          not_pass.pop_back();
          population[place] = childs[index - pop_size].first;
          pop_values[place] = childs[index - pop_size].second;
        }
      }
      std::uniform_real_distribution<long double> mutate(0.0, 1.0);
      for (int i = 0; i < pop_size; ++i) {
        if (mutate(gen) < mut_prob) {
          Mutation(i);
        }
      }
    }
    output_file << std::endl << "##############################" << std::endl;
    //std::cout << "Iterations number is: " << iterations << std::endl;
  }

  void SetClosestStore() {
    clos_store.clear();
    clos_store.resize(shops);
    for (int i = 0; i < shops; ++i) {
      std::vector<SPair1> distances;
      distances.reserve(shops - 1);
      for (int j = 0; j < shops; ++j) {
        if (i == j) {
          continue;
        }
        distances.push_back({j, Dist(stores[i], stores[j])});
      }
      int closest_count = std::min(num_of_clos, static_cast<int>(distances.size()));
      std::nth_element(distances.begin(),
                       distances.begin() + closest_count - 1,
                       distances.end(), Comp1);
      db border = distances[closest_count - 1].second;
      std::vector<SPair1> closest;
      for (int j = 0; j < distances.size(); ++j) {
        if (distances[j].second <= border) {
          closest.push_back(distances[j]);
        }
      }
      std::sort(closest.begin(), closest.end(), Comp1);
      for (int j = 0; j < closest.size(); ++j) {
        clos_store[i].push_back(closest[j].first);
      }
    }
  }

  bool ChangeStore(int before, int after) {
    std::vector<int> old_ans = cur_ans;
    db old_ans_val = cur_ans_val;
    std::vector<int> before_guys(stores[before].guys.begin(),
                                 stores[before].guys.end());
    for (int i = 0; i < static_cast<int>(before_guys.size()); ++i) {
      int guy_num = before_guys[i];
      stores[before].Rem(guy_num, guys[guy_num]);
    }
    db delta = -stores[before].open;
    bool all_moved = true;
    for (int i = 0; i < static_cast<int>(before_guys.size()); ++i) {
      int guy_num = before_guys[i];
      int new_store = after;
      if (!stores[after].can_take(guys[guy_num])) {
        new_store = -1;
        for (int j = 0; j < shops; ++j) {
          int candidate = guy_pref[guy_num][j];
          if (candidate != before && candidate != after &&
              stores[candidate].is_open &&
              stores[candidate].can_take(guys[guy_num])) {
            new_store = candidate;
            break;
          }
        }
      }
      if (new_store == -1) {
        all_moved = false;
        break;
      }
      delta += stores[new_store].add_cost(guys[guy_num]) -
               Dist(stores[before], guys[guy_num]);
      stores[new_store].Add(guy_num, guys[guy_num]);
      guys[guy_num].go_to = new_store;
      cur_ans[guy_num] = new_store;
    }
    if (all_moved) {
      cur_ans_val += delta;
      OneTwoOpt();
      if (cur_ans_val < old_ans_val - cEps) {
        return true;
      }
    }
    cur_ans = old_ans;
    cur_ans_val = old_ans_val;
    SetStoresAndGuys(cur_ans);
    return false;
  }

  bool ChangingStore() {
    int counter = 0;
    int in_total = 0;
    std::vector<int> store_order;
    store_order.reserve(shops);
    for (int i = 0; i < shops; ++i) {
      store_order.push_back(i);
    }
    std::random_device rd;
    std::mt19937 gen(rd());
    bool changed = false;
    auto start = std::chrono::steady_clock::now();
    while (true) {
      auto end = std::chrono::steady_clock::now();
      auto duration = std::chrono::duration_cast<std::chrono::seconds>(end - start);
      if (duration.count() > 60) {
        break;
      }
      std::shuffle(store_order.begin(), store_order.end(), gen);
      bool improved = false;
      for (int i = 0; i < shops; ++i) {
        auto end = std::chrono::steady_clock::now();
        auto duration = std::chrono::duration_cast<std::chrono::seconds>(end - start);
        if (duration.count() > 60) {
          break;
        }
        int before = store_order[i];
        if (!stores[before].is_open) {
          continue;
        }
        for (int j = 0; j < clos_store[before].size(); ++j) {
          int after = clos_store[before][j];
          if (stores[after].is_open) {
            continue;
          }
          std::pair<int, int> change = {before, after};
          if (tabu_list.count(change) > 0 && tabu_list[change] > time) {
            continue;
          }
          ++in_total;
          if (ChangeStore(before, after)) {
            ++counter;
            ++time;
            improved = true;
            changed = true;
            break;
          } else {
            tabu_list[change] = time + tabu_ban;
          }
        }
      }
      if (!improved) {
        break;
      }
    }
    //std::cout << "Counter is:" << counter << " and in total is " << in_total << "\n";
    return changed;
  }

  void SetTabuBan() {
    if (shops < 400) {
      tabu_ban = -1;
    } else {
      tabu_ban = -1;
    }
  }

  bool AddStore(int store) {
    if (stores[store].is_open) {
      return false;
    }
    std::vector<SPair1> candidates;
    for (int i = 0; i < people; ++i) {
      db benefit = Dist(stores[cur_ans[i]], guys[i]) -
                   Dist(stores[store], guys[i]);
      if (benefit > cEps) {
        candidates.push_back({i, benefit / guys[i].demand});
      }
    }
    std::sort(candidates.begin(), candidates.end(), Comp1);
    std::vector<int> selected;
    db selected_demand = 0;
    db total_benefit = 0;
    for (int i = static_cast<int>(candidates.size()) - 1; i >= 0; --i) {
      int guy_num = candidates[i].first;
      if (selected_demand + guys[guy_num].demand > stores[store].cap) {
        continue;
      }
      selected.push_back(guy_num);
      selected_demand += guys[guy_num].demand;
      total_benefit += Dist(stores[cur_ans[guy_num]], guys[guy_num]) -
                       Dist(stores[store], guys[guy_num]);
    }
    if (total_benefit <= stores[store].open + cEps) {
      return false;
    }
    db delta = stores[store].open - total_benefit;
    for (int i = 0; i < static_cast<int>(selected.size()); ++i) {
      int guy_num = selected[i];
      int old_store = cur_ans[guy_num];
      if (stores[old_store].guys.size() == 1) {
        delta -= stores[old_store].open;
      }
      stores[old_store].Rem(guy_num, guys[guy_num]);
      stores[store].Add(guy_num, guys[guy_num]);
      guys[guy_num].go_to = store;
      cur_ans[guy_num] = store;
    }
    cur_ans_val += delta;
    return true;
  } 

  bool AddStores() {
    std::vector<int> store_order;
    store_order.reserve(shops);
    for (int i = 0; i < shops; ++i) {
      store_order.push_back(i);
    }
    std::random_device rd;
    std::mt19937 gen(rd());
    std::shuffle(store_order.begin(), store_order.end(), gen);
    bool changed = false;
    for (int i = 0; i < shops; ++i) {
      int store = store_order[i];
      if (!stores[store].is_open && AddStore(store)) {
        changed = true;
      }
    }
    if (changed) {
      OneTwoOpt();
    }
    return changed;
  }

  bool TryPushOne(int who, int depth = 0) {
    std::vector<int> close_stores;
    for (int i = 0; i < shops; ++i) {
      int store = guy_pref[who][i];
      if (stores[store].is_open) {
        close_stores.push_back(store);
        if (static_cast<int>(close_stores.size()) == close_num) {
          break;
        }
      }
    }
    for (int i = 0; i < static_cast<int>(close_stores.size()); ++i) {
      int store = close_stores[i];
      if (stores[store].can_take(guys[who])) {
        stores[store].Add(who, guys[who]);
        guys[who].go_to = store;
        cur_ans[who] = store;
        return true;
      }
    }
    if (depth == max_depth) {
      return false;
    }
    std::vector<int> swap_candidates;
    int candidate_limit = pot_swaps;
    for (int i = 0; i < static_cast<int>(close_stores.size()); ++i) {
      int store = close_stores[i];
      std::vector<SPair1> store_candidates;
      std::vector<int> store_guys(stores[store].guys.begin(),
                                  stores[store].guys.end());
      for (int j = 0; j < static_cast<int>(store_guys.size()); ++j) {
        int candidate = store_guys[j];
        if (guys[candidate].demand < guys[who].demand &&
            stores[store].taken - guys[candidate].demand +
                    guys[who].demand <=
                stores[store].cap) {
          store_candidates.push_back({candidate, guys[candidate].demand});
        }
      }
      std::sort(store_candidates.begin(), store_candidates.end(), Comp1);
      for (int j = 0; j < static_cast<int>(store_candidates.size()); ++j) {
        swap_candidates.push_back(store_candidates[j].first);
        if (static_cast<int>(swap_candidates.size()) == candidate_limit) {
          break;
        }
      }
      if (static_cast<int>(swap_candidates.size()) == candidate_limit) {
        break;
      }
    }
    for (int i = 0; i < static_cast<int>(swap_candidates.size()); ++i) {
      int kicked = swap_candidates[i];
      int store = guys[kicked].go_to;
      stores[store].Rem(kicked, guys[kicked]);
      stores[store].is_open = true;
      stores[store].Add(who, guys[who]);
      guys[who].go_to = store;
      cur_ans[who] = store;
      guys[kicked].go_to = -1;
      cur_ans[kicked] = -1;
      if (TryPushOne(kicked, depth + 1)) {
        return true;
      }
      stores[store].Rem(who, guys[who]);
      stores[store].is_open = true;
      stores[store].Add(kicked, guys[kicked]);
      guys[kicked].go_to = store;
      cur_ans[kicked] = store;
      guys[who].go_to = -1;
      cur_ans[who] = -1;
    }
    return false;
  }

  bool PushingOneTwoOpt() {
    std::vector<int> not_set;
    for (int i = 0; i < people; ++i) {
      if (guys[i].go_to == -1) {
        not_set.push_back(i);
      }
    }
    std::vector<int> old_ans = cur_ans;
    std::vector<bool> old_open(shops);
    for (int i = 0; i < shops; ++i) {
      old_open[i] = stores[i].is_open;
    }
    db old_ans_val = cur_ans_val;
    bool old_ans_counted = cur_ans_counted;
    std::random_device rd;
    std::mt19937 gen(rd());
    bool found = false;
    db best_value = cInfty;
    std::vector<int> best_pushing_ans;
    for (int retry = 0; retry < global_retries; ++retry) {
      std::vector<int> failed;
      for (int i = 0; i < static_cast<int>(not_set.size()); ++i) {
        int who = not_set[i];
        if (guys[who].go_to == -1 && !TryPushOne(who)) {
          failed.push_back(who);
        }
      }
      if (failed.empty()) {
        for (int i = 0; i < shops; ++i) {
          if (stores[i].guys.empty()) {
            stores[i].is_open = false;
          }
        }
        CountCurAns();
        if (!found || cur_ans_val < best_value) {
          found = true;
          best_value = cur_ans_val;
          best_pushing_ans = cur_ans;
        }
      }
      cur_ans = old_ans;
      cur_ans_val = old_ans_val;
      cur_ans_counted = old_ans_counted;
      CleanStores();
      for (int i = 0; i < people; ++i) {
        guys[i].go_to = cur_ans[i];
        if (cur_ans[i] != -1) {
          stores[cur_ans[i]].Add(i, guys[i]);
        }
      }
      for (int i = 0; i < shops; ++i) {
        if (old_open[i]) {
          stores[i].is_open = true;
        }
      }
      if (failed.empty()) {
        std::shuffle(not_set.begin(), not_set.end(), gen);
        continue;
      }
      std::shuffle(failed.begin(), failed.end(), gen);
      std::shuffle(not_set.begin(), not_set.end(), gen);
      std::vector<bool> failed_mark(people, false);
      for (int i = 0; i < static_cast<int>(failed.size()); ++i) {
        failed_mark[failed[i]] = true;
      }
      std::vector<int> next_order = failed;
      for (int i = 0; i < static_cast<int>(not_set.size()); ++i) {
        if (!failed_mark[not_set[i]]) {
          next_order.push_back(not_set[i]);
        }
      }
      not_set = next_order;
    }
    if (!found) {
      return false;
    }
    cur_ans = best_pushing_ans;
    cur_ans_val = best_value;
    SetStoresAndGuys(cur_ans);
    cur_ans_counted = true;
    return true;
  }

  bool ChangeStore2(int before, int after) {
    std::vector<int> old_ans = cur_ans;
    db old_ans_val = cur_ans_val;
    std::vector<int> before_guys(stores[before].guys.begin(),
                                 stores[before].guys.end());
    for (int i = 0; i < static_cast<int>(before_guys.size()); ++i) {
      int guy_num = before_guys[i];
      stores[before].Rem(guy_num, guys[guy_num]);
      guys[guy_num].go_to = -1;
      cur_ans[guy_num] = -1;
    }
    stores[after].is_open = true;
    cur_ans_counted = false;
    if (PushingOneTwoOpt() && cur_ans_val < old_ans_val - cEps) {
      return true;
    }
    cur_ans = old_ans;
    cur_ans_val = old_ans_val;
    SetStoresAndGuys(cur_ans);
    cur_ans_counted = true;
    return false;
  }

  bool ChangingStore2() {
    int counter = 0;
    int in_total = 0;
    std::vector<int> store_order;
    store_order.reserve(shops);
    for (int i = 0; i < shops; ++i) {
      store_order.push_back(i);
    }
    std::random_device rd;
    std::mt19937 gen(rd());
    bool changed = false;
    auto start = std::chrono::steady_clock::now();
    while (true) {
      auto end = std::chrono::steady_clock::now();
      auto duration = std::chrono::duration_cast<std::chrono::seconds>(end - start);
      if (duration.count() > 60) {
        break;
      }
      std::shuffle(store_order.begin(), store_order.end(), gen);
      bool improved = false;
      for (int i = 0; i < shops; ++i) {
        auto end = std::chrono::steady_clock::now();
        auto duration = std::chrono::duration_cast<std::chrono::seconds>(end - start);
        if (duration.count() > 60) {
          break;
        }
        int before = store_order[i];
        if (!stores[before].is_open) {
          continue;
        }
        for (int j = 0; j < clos_store[before].size(); ++j) {
          int after = clos_store[before][j];
          if (stores[after].is_open) {
            continue;
          }
          std::pair<int, int> change = {before, after};
          if (tabu_list.count(change) > 0 && tabu_list[change] > time) {
            continue;
          }
          ++in_total;
          if (ChangeStore2(before, after)) {
            ++counter;
            ++time;
            improved = true;
            changed = true;
            break;
          } else {
            tabu_list[change] = time + tabu_ban;
          }
        }
      }
      if (!improved) {
        break;
      }
    }
    //std::cout << "Counter is:" << counter << " and in total is " << in_total << "\n";
    return changed;
  }

  void LocalSearch() {
    cur_ans = best_ans;
    CountCurAns();
    SetStoresAndGuys(cur_ans);
    SetTabuBan();
    SetClosestStore();
    ChangingStore();
    //ChangingStore2();
    AddStores();
    /*while (true) {
      bool changed = false;
      changed |= ChangingStore();
      changed |= ChangingStore2();
      changed |= AddStores();
      if (!changed) {
        break;
      }
    }*/
    SetBetter();
  }

  void SetTemperature() {
    temp = 1600000;
    temp_change = 0.9975;
    temp_stop = 40;
  }

  bool AnnealingOneOpt(std::vector<int>& close) {
    bool any_changed = false;
    while (true) {
      bool changed = false;
      for (int ii = 0; ii < static_cast<int>(close.size()); ++ii) {
        int i = close[ii];
        int old_store = guys[i].go_to;
        int best_store = old_store;
        db benefit = 0;
        for (int j = 0; j < shops; ++j) {
          if (j == old_store) {
            continue;
          }
          db other_benefit = stores[old_store].rem_cost(guys[i]) -
                             stores[j].add_cost(guys[i]);
          if (other_benefit > benefit) {
            best_store = j;
            benefit = other_benefit;
          }
        }
        if (benefit > 0) {
          bool old_closed = stores[old_store].guys.size() == 1;
          bool new_opened = !stores[best_store].is_open;
          stores[old_store].Rem(i, guys[i]);
          stores[best_store].Add(i, guys[i]);
          if (old_closed) {
            total_demand -= stores[old_store].cap;
          }
          if (new_opened) {
            total_demand += stores[best_store].cap;
          }
          cur_ans_val -= benefit;
          cur_ans[i] = best_store;
          guys[i].go_to = best_store;
          changed = true;
          any_changed = true;
          break;
        }
      }
      if (!changed) {
        break;
      }
    }
    return any_changed;
  }

  bool AnnealingTwoOpt(std::vector<int>& close) {
    bool any_changed = false;
    while (true) {
      bool changed = false;
      for (int ii = 0; ii < static_cast<int>(close.size()); ++ii) {
        int i = close[ii];
        for (int jj = ii + 1; jj < static_cast<int>(close.size()); ++jj) {
          int j = close[jj];
          if (cur_ans[i] == cur_ans[j]) {
            continue;
          }
          int first_store = cur_ans[i];
          int second_store = cur_ans[j];
          db benefit = stores[first_store].TwoOptBen(guys[i], guys[j]) +
                       stores[second_store].TwoOptBen(guys[j], guys[i]);
          if (benefit > cEps) {
            bool first_closed = stores[first_store].guys.size() == 1;
            bool second_closed = stores[second_store].guys.size() == 1;
            stores[first_store].Rem(i, guys[i]);
            stores[second_store].Rem(j, guys[j]);
            if (first_closed) {
              total_demand -= stores[first_store].cap;
            }
            if (second_closed) {
              total_demand -= stores[second_store].cap;
            }
            bool first_opened = !stores[first_store].is_open;
            bool second_opened = !stores[second_store].is_open;
            stores[second_store].Add(i, guys[i]);
            stores[first_store].Add(j, guys[j]);
            if (first_opened) {
              total_demand += stores[first_store].cap;
            }
            if (second_opened) {
              total_demand += stores[second_store].cap;
            }
            cur_ans_val -= benefit;
            cur_ans[i] = second_store;
            cur_ans[j] = first_store;
            guys[i].go_to = second_store;
            guys[j].go_to = first_store;
            changed = true;
            any_changed = true;
            break;
          }
        }
        if (changed) {
          break;
        }
      }
      if (!changed) {
        break;
      }
    }
    return any_changed;
  }

  void AnnealingOneTwoOpt(int center) {
    std::vector<SPair1> near_stores;
    for (int i = 0; i < shops; ++i) {
      if (i != center && stores[i].is_open) {
        near_stores.push_back({i, Dist(stores[center], stores[i])});
      }
    }
    int store_count = std::min(close_num,
                               static_cast<int>(near_stores.size()));
    if (store_count < static_cast<int>(near_stores.size())) {
      std::nth_element(near_stores.begin(),
                       near_stores.begin() + store_count,
                       near_stores.end(), Comp1);
    }
    std::vector<int> close;
    std::vector<int> center_guys(stores[center].guys.begin(),
                                 stores[center].guys.end());
    for (int i = 0; i < static_cast<int>(center_guys.size()); ++i) {
      close.push_back(center_guys[i]);
    }
    for (int i = 0; i < store_count; ++i) {
      int store = near_stores[i].first;
      std::vector<int> store_guys(stores[store].guys.begin(),
                                  stores[store].guys.end());
      for (int j = 0; j < static_cast<int>(store_guys.size()); ++j) {
        close.push_back(store_guys[j]);
      }
    }
    while (true) {
      bool changed = false;
      changed = changed || AnnealingOneOpt(close);
      SetBetter();
      changed = changed || AnnealingTwoOpt(close);
      SetBetter();
      if (!changed) {
        break;
      }
    }
  }

  db AnnealingStep() {
    std::random_device rd;
    std::mt19937 gen(rd());
    std::vector<int> before_candidates;
    for (int i = 0; i < shops; ++i) {
      if (!stores[i].is_open) {
        continue;
      }
      for (int j = 0; j < static_cast<int>(clos_store[i].size()); ++j) {
        int after = clos_store[i][j];
        if (!stores[after].is_open) {
          before_candidates.push_back(i);
          break;
        }
      }
    }
    std::uniform_int_distribution<int> before_dist(
        0, static_cast<int>(before_candidates.size()) - 1);
    int before = before_candidates[before_dist(gen)];
    std::vector<int> after_candidates;
    for (int i = 0; i < static_cast<int>(clos_store[before].size()); ++i) {
      int after = clos_store[before][i];
      if (!stores[after].is_open) {
        after_candidates.push_back(after);
      }
    }
    std::uniform_int_distribution<int> after_dist(
        0, static_cast<int>(after_candidates.size()) - 1);
    int after = after_candidates[after_dist(gen)];
    std::vector<int> old_ans = cur_ans;
    db old_ans_val = cur_ans_val;
    db old_total_demand = total_demand;
    std::vector<int> before_guys(stores[before].guys.begin(),
                                 stores[before].guys.end());
    for (int i = 0; i < static_cast<int>(before_guys.size()); ++i) {
      int guy = before_guys[i];
      stores[before].Rem(guy, guys[guy]);
    }
    total_demand -= stores[before].cap;
    db delta = -stores[before].open;
    bool placed = true;
    for (int i = 0; i < static_cast<int>(before_guys.size()); ++i) {
      int guy = before_guys[i];
      int new_store = after;
      if (!stores[new_store].can_take(guys[guy])) {
        new_store = -1;
        for (int j = 0; j < shops; ++j) {
          int candidate = guy_pref[guy][j];
          if (candidate != before && candidate != after &&
              stores[candidate].is_open &&
              stores[candidate].can_take(guys[guy])) {
            new_store = candidate;
            break;
          }
        }
      }
      if (new_store == -1) {
        placed = false;
        break;
      }
      delta += stores[new_store].add_cost(guys[guy]) -
               Dist(stores[before], guys[guy]);
      bool opened = !stores[new_store].is_open;
      stores[new_store].Add(guy, guys[guy]);
      if (opened) {
        total_demand += stores[new_store].cap;
      }
      guys[guy].go_to = new_store;
      cur_ans[guy] = new_store;
    }
    if (!placed) {
      cur_ans = old_ans;
      cur_ans_val = old_ans_val;
      SetStoresAndGuys(cur_ans);
      cur_ans_counted = true;
      total_demand = old_total_demand;
      return 0;
    }
    cur_ans_val += delta;
    AnnealingOneTwoOpt(before);
    AnnealingOneTwoOpt(after);
    delta = cur_ans_val - old_ans_val;
    bool accept = delta < 0;
    if (!accept) {
      std::uniform_real_distribution<long double> prob_dist(0.0L, 1.0L);
      long double prob = std::exp(-delta / temp);
      accept = prob_dist(gen) < prob;
    }
    if (accept) {
      SetBetter();
      return delta;
    }
    cur_ans = old_ans;
    cur_ans_val = old_ans_val;
    SetStoresAndGuys(cur_ans);
    cur_ans_counted = true;
    total_demand = old_total_demand;
    return delta;
  }

  void AnnealingInsertStep() {
    std::random_device rd;
    std::mt19937 gen(rd());
    std::vector<int> closed_stores;
    for (int i = 0; i < shops; ++i) {
      if (!stores[i].is_open) {
        closed_stores.push_back(i);
      }
    }
    if (closed_stores.empty()) {
      return;
    }
    std::uniform_int_distribution<int> store_dist(
        0, static_cast<int>(closed_stores.size()) - 1);
    int store = closed_stores[store_dist(gen)];
    std::vector<SPair1> candidates;
    for (int i = 0; i < people; ++i) {
      db benefit = Dist(stores[cur_ans[i]], guys[i]) -
                   Dist(stores[store], guys[i]);
      if (benefit > 0) {
        candidates.push_back({i, benefit / guys[i].demand});
      }
    }
    std::sort(candidates.begin(), candidates.end(), Comp1);
    std::vector<int> selected;
    db selected_demand = 0;
    for (int i = static_cast<int>(candidates.size()) - 1; i >= 0; --i) {
      int guy = candidates[i].first;
      if (selected_demand + guys[guy].demand <= stores[store].cap) {
        selected.push_back(guy);
        selected_demand += guys[guy].demand;
      }
    }
    if (selected.empty()) {
      return;
    }
    db old_ans_val = cur_ans_val;
    db old_total_demand = total_demand;
    std::vector<std::pair<int, int>> old_places;
    std::set<int> saved_people;
    db delta = stores[store].open;
    for (int i = 0; i < static_cast<int>(selected.size()); ++i) {
      int guy = selected[i];
      int old_store = cur_ans[guy];
      old_places.push_back({guy, old_store});
      saved_people.insert(guy);
      delta += Dist(stores[store], guys[guy]) -
               Dist(stores[old_store], guys[guy]);
      if (stores[old_store].guys.size() == 1) {
        delta -= stores[old_store].open;
        total_demand -= stores[old_store].cap;
      }
      stores[old_store].Rem(guy, guys[guy]);
      stores[store].Add(guy, guys[guy]);
      guys[guy].go_to = store;
      cur_ans[guy] = store;
    }
    total_demand += stores[store].cap;
    cur_ans_val += delta;

    std::vector<SPair1> near_stores;
    for (int i = 0; i < shops; ++i) {
      if (i != store && stores[i].is_open) {
        near_stores.push_back({i, Dist(stores[store], stores[i])});
      }
    }
    int store_count = std::min(close_num,
                               static_cast<int>(near_stores.size()));
    if (store_count < static_cast<int>(near_stores.size())) {
      std::nth_element(near_stores.begin(), near_stores.begin() + store_count,
                       near_stores.end(), Comp1);
    }
    for (int i = 0; i < store_count; ++i) {
      int store_num = near_stores[i].first;
      std::vector<int> store_guys(stores[store_num].guys.begin(),
                                  stores[store_num].guys.end());
      for (int j = 0; j < static_cast<int>(store_guys.size()); ++j) {
        int guy = store_guys[j];
        if (saved_people.count(guy) == 0) {
          saved_people.insert(guy);
          old_places.push_back({guy, guys[guy].go_to});
        }
      }
    }
    AnnealingOneTwoOpt(store);
    delta = cur_ans_val - old_ans_val;

    bool accept = delta < 0;
    if (!accept) {
      std::uniform_real_distribution<long double> prob_dist(0.0L, 1.0L);
      long double prob = std::exp(-delta / temp);
      accept = prob_dist(gen) < prob;
    }
    if (accept) {
      SetBetter();
      return;
    }
    for (int i = 0; i < static_cast<int>(old_places.size()); ++i) {
      int guy = old_places[i].first;
      stores[guys[guy].go_to].Rem(guy, guys[guy]);
    }
    for (int i = 0; i < static_cast<int>(old_places.size()); ++i) {
      int guy = old_places[i].first;
      int old_store = old_places[i].second;
      stores[old_store].Add(guy, guys[guy]);
      guys[guy].go_to = old_store;
      cur_ans[guy] = old_store;
    }
    cur_ans_val = old_ans_val;
    cur_ans_counted = true;
    total_demand = old_total_demand;
  }

  int AnnealingRemoveStep() {
    std::random_device rd;
    std::mt19937 gen(rd());
    std::vector<int> store_order;
    for (int i = 0; i < shops; ++i) {
      if (stores[i].is_open) {
        store_order.push_back(i);
      }
    }
    std::shuffle(store_order.begin(), store_order.end(), gen);
    int accepted = 0;
    for (int i = 0; i < static_cast<int>(store_order.size()); ++i) {
      int store = store_order[i];
      if (!stores[store].is_open) {
        continue;
      }
      db old_ans_val = cur_ans_val;
      db old_total_demand = total_demand;
      std::vector<int> store_guys(stores[store].guys.begin(),
                                  stores[store].guys.end());
      std::vector<std::pair<int, int>> old_places;
      std::set<int> saved_people;
      std::shuffle(store_guys.begin(), store_guys.end(), gen);
      for (int j = 0; j < static_cast<int>(store_guys.size()); ++j) {
        int guy = store_guys[j];
        old_places.push_back({guy, store});
        saved_people.insert(guy);
        stores[store].Rem(guy, guys[guy]);
      }
      total_demand -= stores[store].cap;
      db delta = -stores[store].open;
      bool placed = true;
      for (int j = 0; j < static_cast<int>(store_guys.size()); ++j) {
        int guy = store_guys[j];
        int new_store = -1;
        for (int k = 0; k < shops; ++k) {
          int candidate = guy_pref[guy][k];
          if (candidate != store && stores[candidate].is_open &&
              stores[candidate].can_take(guys[guy])) {
            new_store = candidate;
            break;
          }
        }
        if (new_store == -1) {
          placed = false;
          break;
        }
        delta += Dist(stores[new_store], guys[guy]) -
                 Dist(stores[store], guys[guy]);
        stores[new_store].Add(guy, guys[guy]);
        guys[guy].go_to = new_store;
        cur_ans[guy] = new_store;
      }
      bool accept = false;
      if (placed) {
        cur_ans_val += delta;
        std::vector<SPair1> near_stores;
        for (int j = 0; j < shops; ++j) {
          if (j != store && stores[j].is_open) {
            near_stores.push_back({j, Dist(stores[store], stores[j])});
          }
        }
        int store_count = std::min(close_num,
                                   static_cast<int>(near_stores.size()));
        if (store_count < static_cast<int>(near_stores.size())) {
          std::nth_element(near_stores.begin(),
                           near_stores.begin() + store_count,
                           near_stores.end(), Comp1);
        }
        for (int j = 0; j < store_count; ++j) {
          int store_num = near_stores[j].first;
          std::vector<int> close_guys(stores[store_num].guys.begin(),
                                      stores[store_num].guys.end());
          for (int k = 0; k < static_cast<int>(close_guys.size()); ++k) {
            int guy = close_guys[k];
            if (saved_people.count(guy) == 0) {
              saved_people.insert(guy);
              old_places.push_back({guy, guys[guy].go_to});
            }
          }
        }
        AnnealingOneTwoOpt(store);
        delta = cur_ans_val - old_ans_val;
        accept = delta < 0;
      }
      if (placed && !accept) {
        std::uniform_real_distribution<long double> prob_dist(0.0L, 1.0L);
        long double prob = std::exp(-delta / temp);
        accept = prob_dist(gen) < prob;
      }
      if (accept) {
        ++accepted;
        SetBetter();
        continue;
      }
      for (int j = 0; j < static_cast<int>(old_places.size()); ++j) {
        int guy = old_places[j].first;
        if (placed || cur_ans[guy] != store) {
          stores[guys[guy].go_to].Rem(guy, guys[guy]);
        }
      }
      for (int j = 0; j < static_cast<int>(old_places.size()); ++j) {
        int guy = old_places[j].first;
        int old_store = old_places[j].second;
        stores[old_store].Add(guy, guys[guy]);
        guys[guy].go_to = old_store;
        cur_ans[guy] = old_store;
      }
      cur_ans_val = old_ans_val;
      cur_ans_counted = true;
      total_demand = old_total_demand;
    }
    return accepted;
  }

  void FindTotalDemand() {
    total_demand = 0;
    first_demand = 0;
    for (int i = 0; i < shops; ++i) {
      if (stores[i].is_open) {
        total_demand += stores[i].cap;
        first_demand += stores[i].cap;
      }
    }
  }

  void Annealing1() {
    cur_ans = best_ans;
    CountCurAns();
    SetStoresAndGuys(cur_ans);
    SetClosestStore();
    FindTotalDemand();
    SetTemperature();
    int iter = 0;
    std::queue<long double> delta_queue;
    long double delta_sum = 0;
    while (temp > temp_stop) {
      db delta = AnnealingStep();
      delta_queue.push(delta);
      delta_sum += delta;
      if (delta_queue.size() > 20) {
        delta_sum -= delta_queue.front();
        delta_queue.pop();
      }
      if (iter % 1000 == 20) {
        long double delta_avg = delta_sum / delta_queue.size();
        /*std::cout << "Temp par: " << iter << " " << temp << " " << delta_avg << " "
                  << -delta_avg / temp << " " << std::exp(-delta_avg / temp) << " "
                  << best_ans_val << " " << cur_ans_val << std::endl;*/
      }
      temp *= temp_change;
      ++iter;
      /*if (iter % 1000 == 0) {
        OneTwoOpt();
        //std::cout <<  "Iters done " << iter << ", " << cur_ans_val << std::endl;
      }*/
      if (total_demand / first_demand < high_dif) {
        AnnealingInsertStep();
      } else {
        AnnealingRemoveStep();
      }
    }
    //std::cout << "Iters done " << iter << '\n';
  }

  db AnnealingChangeStore(int before, int after) {
    std::random_device rd;
    std::mt19937 gen(rd());
    std::vector<int> old_ans = cur_ans;
    db old_ans_val = cur_ans_val;
    std::vector<int> before_guys(stores[before].guys.begin(),
                                 stores[before].guys.end());
    for (int i = 0; i < static_cast<int>(before_guys.size()); ++i) {
      int guy_num = before_guys[i];
      stores[before].Rem(guy_num, guys[guy_num]);
    }
    db delta = -stores[before].open;
    bool all_moved = true;
    for (int i = 0; i < static_cast<int>(before_guys.size()); ++i) {
      int guy_num = before_guys[i];
      int new_store = after;
      if (!stores[after].can_take(guys[guy_num])) {
        new_store = -1;
        for (int j = 0; j < shops; ++j) {
          int candidate = guy_pref[guy_num][j];
          if (candidate != before && candidate != after &&
              stores[candidate].is_open &&
              stores[candidate].can_take(guys[guy_num])) {
            new_store = candidate;
            break;
          }
        }
      }
      if (new_store == -1) {
        all_moved = false;
        break;
      }
      delta += stores[new_store].add_cost(guys[guy_num]) -
               Dist(stores[before], guys[guy_num]);
      stores[new_store].Add(guy_num, guys[guy_num]);
      guys[guy_num].go_to = new_store;
      cur_ans[guy_num] = new_store;
    }
    if (all_moved) {
      cur_ans_val += delta;
      OneTwoOpt();
      if (cur_ans_val < old_ans_val - cEps) {
        return cur_ans_val - old_ans_val;
      } else {
        delta = cur_ans_val - old_ans_val;
        std::uniform_real_distribution<long double> prob_dist(0.0L, 1.0L);
        long double prob = std::exp(-delta / temp);
        if(prob_dist(gen) < prob) {
          return delta;
        }
      }
    }
    cur_ans = old_ans;
    cur_ans_val = old_ans_val;
    SetStoresAndGuys(cur_ans);
    return 0;
  }

  void SetTemperature2() {
    temp = 1600000;
    temp_change = 0.9975;
    temp_stop = 1E-3;
  }

  void Annealing2() {
    cur_ans = best_ans;
    CountCurAns();
    SetStoresAndGuys(cur_ans);
    SetClosestStore();
    SetTemperature2();
    int iter = 0;
    std::queue<long double> delta_queue;
    long double delta_sum = 0;
    std::vector<int> store_order;
    store_order.reserve(shops);
    for (int i = 0; i < shops; ++i) {
      store_order.push_back(i);
    }
    std::random_device rd;
    std::mt19937 gen(rd());
    while (temp > temp_stop) {
      std::shuffle(store_order.begin(), store_order.end(), gen);
      bool improved = false;
      for (int i = 0; i < shops; ++i) {
        int before = store_order[i];
        if (!stores[before].is_open) {
          continue;
        }
        for (int j = 0; j < clos_store[before].size(); ++j) {
          int after = clos_store[before][j];
          if (stores[after].is_open) {
            continue;
          }
          db delta = AnnealingChangeStore(before, after);
          delta_queue.push(delta);
          delta_sum += delta;
          if (delta_queue.size() > 20) {
            delta_sum -= delta_queue.front();
            delta_queue.pop();
          }
          if (iter % 1000 == 20) {
            long double delta_avg = delta_sum / delta_queue.size();
            /*std::cout << "Temp par: " << iter << " " << temp << " " << delta_avg << " "
                      << -delta_avg / temp << " " << std::exp(-delta_avg / temp) << " "
                      << best_ans_val << " " << cur_ans_val << std::endl;*/
          }
          temp *= temp_change;
          ++iter;
          if (total_demand / first_demand < high_dif) {
            AnnealingInsertStep();
          } else {
            AnnealingRemoveStep();
          }
          break;
        }
      }
    }
    //std::cout << "Iters done " << iter << '\n';
  }

  struct PushPullPlan {
    std::vector<std::pair<int, int>> rem;
    std::vector<std::pair<int, int>> push;
    int unset = -1;
    bool is_valid = false;
    db metric = 0;
  };

  std::vector<PushPullPlan> LeastDemand(PushPullPlan& plan, int how_many = 2) {
    std::vector<PushPullPlan> result;
    int current = plan.unset;
    std::vector<PushPullPlan> candidates;
    std::vector<SPair1> order;
    int open_seen = 0;
    for (int i = 0; i < shops && open_seen < close_num; ++i) {
      int store = guy_pref[current][i];
      if (!stores[store].is_open) {
        continue;
      }
      ++open_seen;
      if (stores[store].can_take(guys[current])) {
        continue;
      }
      std::vector<int> store_guys(stores[store].guys.begin(),
                                  stores[store].guys.end());
      for (int j = 0; j < static_cast<int>(store_guys.size()); ++j) {
        int kicked = store_guys[j];
        if (stores[store].taken - guys[kicked].demand +
                guys[current].demand > stores[store].cap) {
          continue;
        }
        PushPullPlan next = plan;
        next.rem.push_back({kicked, store});
        next.push.push_back({current, store});
        next.unset = kicked;
        next.metric += Dist(stores[store], guys[current]) -
                       beam_coef * third_dist[current];
        next.metric += beam_coef * third_dist[kicked] -
                       Dist(stores[store], guys[kicked]);
        candidates.push_back(next);
        order.push_back({static_cast<int>(candidates.size()) - 1,
                         guys[kicked].demand});
      }
    }
    std::sort(order.begin(), order.end(), Comp1);
    int left = std::min(how_many, static_cast<int>(order.size()));
    for (int i = 0; i < left; ++i) {
      result.push_back(candidates[order[i].first]);
    }
    return result;
  }

  std::vector<PushPullPlan> MaxClosDif(PushPullPlan& plan, int how_many = 2) {
    std::vector<PushPullPlan> result;
    int current = plan.unset;
    std::vector<PushPullPlan> candidates;
    std::vector<SPair1> order;
    int open_seen = 0;
    for (int i = 0; i < shops && open_seen < close_num; ++i) {
      int store = guy_pref[current][i];
      if (!stores[store].is_open) {
        continue;
      }
      ++open_seen;
      if (stores[store].can_take(guys[current])) {
        continue;
      }
      std::vector<int> store_guys(stores[store].guys.begin(),
                                  stores[store].guys.end());
      for (int j = 0; j < static_cast<int>(store_guys.size()); ++j) {
        int kicked = store_guys[j];
        if (stores[store].taken - guys[kicked].demand +
                guys[current].demand > stores[store].cap) {
          continue;
        }
        PushPullPlan next = plan;
        next.rem.push_back({kicked, store});
        next.push.push_back({current, store});
        next.unset = kicked;
        next.metric += Dist(stores[store], guys[current]) -
                       beam_coef * third_dist[current];
        next.metric += beam_coef * third_dist[kicked] -
                       Dist(stores[store], guys[kicked]);
        candidates.push_back(next);
        int closest = guy_pref[kicked][0];
        db benefit = Dist(stores[store], guys[kicked]) -
                     Dist(stores[closest], guys[kicked]);
        order.push_back({static_cast<int>(candidates.size()) - 1, -benefit});
      }
    }
    std::sort(order.begin(), order.end(), Comp1);
    int left = std::min(how_many, static_cast<int>(order.size()));
    for (int i = 0; i < left; ++i) {
      result.push_back(candidates[order[i].first]);
    }
    return result;
  }

  std::vector<PushPullPlan> MaxClosOpenDif(PushPullPlan& plan, int how_many = 2) {
    std::vector<PushPullPlan> result;
    int current = plan.unset;
    std::vector<PushPullPlan> candidates;
    std::vector<SPair1> order;
    int open_seen = 0;
    for (int i = 0; i < shops && open_seen < close_num; ++i) {
      int store = guy_pref[current][i];
      if (!stores[store].is_open) {
        continue;
      }
      ++open_seen;
      if (stores[store].can_take(guys[current])) {
        continue;
      }
      std::vector<int> store_guys(stores[store].guys.begin(),
                                  stores[store].guys.end());
      for (int j = 0; j < static_cast<int>(store_guys.size()); ++j) {
        int kicked = store_guys[j];
        if (stores[store].taken - guys[kicked].demand +
                guys[current].demand > stores[store].cap) {
          continue;
        }
        int closest_open;
        for (int k = 0; k < shops; ++k) {
          int candidate_store = guy_pref[kicked][k];
          if (stores[candidate_store].is_open) {
            closest_open = candidate_store;
            break;
          }
        }
        PushPullPlan next = plan;
        next.rem.push_back({kicked, store});
        next.push.push_back({current, store});
        next.unset = kicked;
        next.metric += Dist(stores[store], guys[current]) -
                       beam_coef * third_dist[current];
        next.metric += beam_coef * third_dist[kicked] -
                       Dist(stores[store], guys[kicked]);
        candidates.push_back(next);
        db benefit = Dist(stores[store], guys[kicked]) -
                     Dist(stores[closest_open], guys[kicked]);
        order.push_back({static_cast<int>(candidates.size()) - 1, -benefit});
      }
    }
    std::sort(order.begin(), order.end(), Comp1);
    int left = std::min(how_many, static_cast<int>(order.size()));
    for (int i = 0; i < left; ++i) {
      result.push_back(candidates[order[i].first]);
    }
    return result;
  }

  bool BeamOneOpt(int who) {
    PushPullPlan initial;
    initial.unset = who;
    for (int i = 0; i < shops; ++i) {
      if (stores[i].is_open) {
        initial.metric += stores[i].open;
      }
    }
    for (int i = 0; i < people; ++i) {
      if (cur_ans[i] == -1) {
        initial.metric += beam_coef * third_dist[i];
      } else {
        initial.metric += Dist(stores[cur_ans[i]], guys[i]);
      }
    }
    std::vector<PushPullPlan> beam;
    beam.push_back(initial);
    PushPullPlan best_valid;
    bool valid_found = false;
    for (int depth = 0; depth <= max_depth; ++depth) {
      std::vector<PushPullPlan> invalid_plans;
      for (int plan_num = 0; plan_num < static_cast<int>(beam.size()); ++plan_num) {
        PushPullPlan plan = beam[plan_num];
        for (int i = 0; i < static_cast<int>(plan.push.size()); ++i) {
          if (i < static_cast<int>(plan.rem.size())) {
            int rem_guy = plan.rem[i].first;
            int rem_store = plan.rem[i].second;
            stores[rem_store].guys.erase(rem_guy);
            stores[rem_store].taken -= guys[rem_guy].demand;
            guys[rem_guy].go_to = -1;
            cur_ans[rem_guy] = -1;
          }
          int push_guy = plan.push[i].first;
          int push_store = plan.push[i].second;
          stores[push_store].guys.insert(push_guy);
          stores[push_store].taken += guys[push_guy].demand;
          guys[push_guy].go_to = push_store;
          cur_ans[push_guy] = push_store;
        }
        int current = plan.unset;
        std::vector<int> close_stores;
        for (int i = 0; i < shops; ++i) {
          int store = guy_pref[current][i];
          if (stores[store].is_open) {
            close_stores.push_back(store);
            if (static_cast<int>(close_stores.size()) == close_num) {
              break;
            }
          }
        }
        for (int i = 0; i < static_cast<int>(close_stores.size()); ++i) {
          int store = close_stores[i];
          if (stores[store].can_take(guys[current])) {
            stores[store].guys.insert(current);
            stores[store].taken += guys[current].demand;
            guys[current].go_to = store;
            cur_ans[current] = store;
            PushPullPlan next = plan;
            next.push.push_back({current, store});
            next.unset = -1;
            next.is_valid = true;
            next.metric += Dist(stores[store], guys[current]) -
                           beam_coef * third_dist[current];
            if (!valid_found || next.metric < best_valid.metric) {
              valid_found = true;
              best_valid = next;
            }
            stores[store].guys.erase(current);
            stores[store].taken -= guys[current].demand;
            guys[current].go_to = -1;
            cur_ans[current] = -1;
          }
        }
        if (depth != max_depth) {
          std::vector<PushPullPlan> candidates = LeastDemand(plan);
          std::vector<PushPullPlan> new_candidates = MaxClosDif(plan);
          for (int j = 0; j < static_cast<int>(new_candidates.size()); ++j) {
            bool already_added = false;
            for (int k = 0; k < static_cast<int>(candidates.size()); ++k) {
              if (candidates[k].rem.back() == new_candidates[j].rem.back()) {
                already_added = true;
                break;
              }
            }
            if (!already_added) {
              candidates.push_back(new_candidates[j]);
            }
          }
          new_candidates = MaxClosOpenDif(plan);
          for (int j = 0; j < static_cast<int>(new_candidates.size()); ++j) {
            bool already_added = false;
            for (int k = 0; k < static_cast<int>(candidates.size()); ++k) {
              if (candidates[k].rem.back() == new_candidates[j].rem.back()) {
                already_added = true;
                break;
              }
            }
            if (!already_added) {
              candidates.push_back(new_candidates[j]);
            }
          }
          for (int j = 0; j < static_cast<int>(candidates.size()); ++j) {
            int kicked = candidates[j].rem.back().first;
            int candidate_store = candidates[j].rem.back().second;
            int pushed = candidates[j].push.back().first;
            stores[candidate_store].guys.erase(kicked);
            stores[candidate_store].taken -= guys[kicked].demand;
            guys[kicked].go_to = -1;
            cur_ans[kicked] = -1;
            stores[candidate_store].guys.insert(pushed);
            stores[candidate_store].taken += guys[pushed].demand;
            guys[pushed].go_to = candidate_store;
            cur_ans[pushed] = candidate_store;
            invalid_plans.push_back(candidates[j]);
            stores[candidate_store].guys.erase(pushed);
            stores[candidate_store].taken -= guys[pushed].demand;
            guys[pushed].go_to = -1;
            cur_ans[pushed] = -1;
            stores[candidate_store].guys.insert(kicked);
            stores[candidate_store].taken += guys[kicked].demand;
            guys[kicked].go_to = candidate_store;
            cur_ans[kicked] = candidate_store;
          }
        }
        for (int i = static_cast<int>(plan.push.size()) - 1; i >= 0; --i) {
          int push_guy = plan.push[i].first;
          int push_store = plan.push[i].second;
          stores[push_store].guys.erase(push_guy);
          stores[push_store].taken -= guys[push_guy].demand;
          guys[push_guy].go_to = -1;
          cur_ans[push_guy] = -1;
          if (i < static_cast<int>(plan.rem.size())) {
            int rem_guy = plan.rem[i].first;
            int rem_store = plan.rem[i].second;
            stores[rem_store].guys.insert(rem_guy);
            stores[rem_store].taken += guys[rem_guy].demand;
            guys[rem_guy].go_to = rem_store;
            cur_ans[rem_guy] = rem_store;
          }
        }
      }
      if (invalid_plans.empty()) {
        break;
      }
      std::vector<SPair1> plan_order;
      for (int i = 0; i < static_cast<int>(invalid_plans.size()); ++i) {
        plan_order.push_back({i, invalid_plans[i].metric});
      }
      std::sort(plan_order.begin(), plan_order.end(), Comp1);
      beam.clear();
      int left = std::min(beam_const, static_cast<int>(plan_order.size()));
      for (int i = 0; i < left; ++i) {
        beam.push_back(invalid_plans[plan_order[i].first]);
      }
    }
    if (valid_found) {
      for (int i = 0; i < static_cast<int>(best_valid.push.size()); ++i) {
        if (i < static_cast<int>(best_valid.rem.size())) {
          int rem_guy = best_valid.rem[i].first;
          int rem_store = best_valid.rem[i].second;
          stores[rem_store].guys.erase(rem_guy);
          stores[rem_store].taken -= guys[rem_guy].demand;
          guys[rem_guy].go_to = -1;
          cur_ans[rem_guy] = -1;
        }
        int push_guy = best_valid.push[i].first;
        int push_store = best_valid.push[i].second;
        stores[push_store].guys.insert(push_guy);
        stores[push_store].taken += guys[push_guy].demand;
        guys[push_guy].go_to = push_store;
        cur_ans[push_guy] = push_store;
      }
      CountCurAns();
      return true;
    }
    return false;
  }

  void SetThirdDist() {
    third_dist.clear();
    third_dist.resize(people);
    for (int i = 0; i < people; ++i) {
      int open_count = 0;
      int last_open_pos = -1;
      int chosen_store = -1;
      for (int j = 0; j < shops; ++j) {
        int store = guy_pref[i][j];
        if (stores[store].is_open) {
          ++open_count;
          last_open_pos = j;
          if (open_count == 3) {
            chosen_store = store;
            break;
          }
        }
      }
      if (chosen_store == -1 && open_count > 0) {
        int closed_needed = 2 * (3 - open_count);
        int closed_count = 0;
        for (int j = last_open_pos + 1; j < shops; ++j) {
          int store = guy_pref[i][j];
          if (!stores[store].is_open) {
            ++closed_count;
            if (closed_count == closed_needed) {
              chosen_store = store;
              break;
            }
          }
        }
      }
      if (chosen_store == -1) {
        chosen_store = guy_pref[i][shops - 1];
      }
      third_dist[i] = Dist(stores[chosen_store], guys[i]);
    }
  }

  bool BeamOneTwoOpt() {
    int ii = 0;
    bool changed = false;
    while (true) {
      bool improved = false;
      for (int jj = 0; jj < people; ++jj) {
        int i = (ii + jj) % people;
        std::vector<int> before_ans = cur_ans;
        int before_place = cur_ans[i];
        db before_metric = cur_ans_val;
        stores[before_place].guys.erase(i);
        stores[before_place].taken -= guys[i].demand;
        guys[i].go_to = -1;
        cur_ans[i] = -1;
        if (BeamOneOpt(i) && cur_ans_val < before_metric - cEps) {
          improved = true;
          changed = true;
          ii = (i + 1) % people;
          break;
        }
        for (int guy = 0; guy < people; ++guy) {
          if (cur_ans[guy] == before_ans[guy]) {
            continue;
          }
          if (cur_ans[guy] != -1) {
            int store = cur_ans[guy];
            stores[store].guys.erase(guy);
            stores[store].taken -= guys[guy].demand;
          }
          int store = before_ans[guy];
          stores[store].guys.insert(guy);
          stores[store].taken += guys[guy].demand;
          guys[guy].go_to = store;
          cur_ans[guy] = store;
        }
        cur_ans_val = before_metric;
        cur_ans_counted = true;
      }
      if (!improved) {
        break;
      }
    }
    return changed;
  }

  bool BeamChangeStore(int before1, int before2, int after1, int after2) {
    std::vector<int> old_ans = cur_ans;
    db old_ans_val = cur_ans_val;
    std::vector<int> before_guys(stores[before1].guys.begin(),
                                 stores[before1].guys.end());
    if (before2 != before1) {
      std::vector<int> second_guys(stores[before2].guys.begin(),
                                   stores[before2].guys.end());
      for (int i = 0; i < static_cast<int>(second_guys.size()); ++i) {
        before_guys.push_back(second_guys[i]);
      }
    }
    for (int i = 0; i < static_cast<int>(before_guys.size()); ++i) {
      int guy = before_guys[i];
      int before = cur_ans[guy];
      stores[before].Rem(guy, guys[guy]);
      guys[guy].go_to = -1;
      cur_ans[guy] = -1;
    }
    stores[before1].is_open = false;
    stores[before2].is_open = false;
    stores[after1].is_open = true;
    stores[after2].is_open = true;
    bool all_moved = true;
    for (int i = 0; i < static_cast<int>(before_guys.size()); ++i) {
      int guy = before_guys[i];
      int after1_pref = 0;
      while (guy_pref[guy][after1_pref] != after1) {
        ++after1_pref;
      }
      int first_open_pref = 0;
      while (!stores[guy_pref[guy][first_open_pref]].is_open) {
        ++first_open_pref;
      }
      std::swap(guy_pref[guy][first_open_pref], guy_pref[guy][after1_pref]);
      int after2_pref = -1;
      int second_open_pref = -1;
      if (after2 != after1) {
        after2_pref = 0;
        while (guy_pref[guy][after2_pref] != after2) {
          ++after2_pref;
        }
        second_open_pref = 0;
        while (second_open_pref == first_open_pref ||
               !stores[guy_pref[guy][second_open_pref]].is_open) {
          ++second_open_pref;
        }
        std::swap(guy_pref[guy][second_open_pref],
                  guy_pref[guy][after2_pref]);
      }
      bool moved = BeamOneOpt(guy);
      if (after2 != after1) {
        std::swap(guy_pref[guy][second_open_pref],
                  guy_pref[guy][after2_pref]);
      }
      std::swap(guy_pref[guy][first_open_pref], guy_pref[guy][after1_pref]);
      if (!moved) {
        all_moved = false;
        break;
      }
    }
    if (all_moved && cur_ans_val < old_ans_val - cEps) {
      return true;
    }
    cur_ans = old_ans;
    cur_ans_val = old_ans_val;
    SetStoresAndGuys(cur_ans);
    cur_ans_counted = true;
    return false;
  }

  bool BeamChangingStore() {
    std::vector<int> store_order;
    store_order.reserve(shops);
    for (int i = 0; i < shops; ++i) {
      store_order.push_back(i);
    }
    std::random_device rd;
    std::mt19937 gen(rd());
    bool changed = false;
    auto start = std::chrono::steady_clock::now();
    while (true) {
      auto end = std::chrono::steady_clock::now();
      auto duration =
          std::chrono::duration_cast<std::chrono::seconds>(end - start);
      if (duration.count() > 180) {
        break;
      }
      std::shuffle(store_order.begin(), store_order.end(), gen);
      bool improved = false;
      for (int i = 0; i < shops; ++i) {
        end = std::chrono::steady_clock::now();
        duration =
            std::chrono::duration_cast<std::chrono::seconds>(end - start);
        if (duration.count() > 180) {
          break;
        }
        int after1 = store_order[i];
        if (stores[after1].is_open) {
          continue;
        }
        bool accepted = false;
        for (int j = 0; j < static_cast<int>(clos_store[after1].size()); ++j) {
          int before1 = clos_store[after1][j];
          if (!stores[before1].is_open) {
            continue;
          }
          for (int k = 0; k < static_cast<int>(clos_store[before1].size()); ++k) {
            int after2 = clos_store[before1][k];
            if (stores[after2].is_open) {
              continue;
            }
            for (int l = 0; l < static_cast<int>(clos_store[after2].size()); ++l) {
              int before2 = clos_store[after2][l];
              if (!stores[before2].is_open) {
                continue;
              }
              if (BeamChangeStore(before1, before2, after1, after2)) {
                improved = true;
                changed = true;
                accepted = true;
                break;
              }
            }
            if (accepted) {
              break;
            }
          }
          if (accepted) {
            break;
          }
        }
      }
      if (!improved) {
        break;
      }
    }
    return changed;
  }

  bool BeamAddStore() {
    bool changed = false;
    for (int store = 0; store < shops; ++store) {
      if (stores[store].is_open) {
        continue;
      }
      std::vector<int> old_ans = cur_ans;
      db old_ans_val = cur_ans_val;
      stores[store].is_open = true;
      BeamOneTwoOpt();
      if (cur_ans_val < old_ans_val - cEps) {
        changed = true;
        continue;
      }
      cur_ans = old_ans;
      cur_ans_val = old_ans_val;
      SetStoresAndGuys(cur_ans);
      cur_ans_counted = true;
    }
    return changed;
  }

  bool BeamRemStore() {
    bool changed = false;
    for (int store = 0; store < shops; ++store) {
      if (!stores[store].is_open) {
        continue;
      }
      std::vector<int> old_ans = cur_ans;
      db old_ans_val = cur_ans_val;
      std::vector<int> store_guys(stores[store].guys.begin(),
                                  stores[store].guys.end());
      for (int i = 0; i < static_cast<int>(store_guys.size()); ++i) {
        int guy = store_guys[i];
        stores[store].Rem(guy, guys[guy]);
        guys[guy].go_to = -1;
        cur_ans[guy] = -1;
      }
      stores[store].is_open = false;
      bool all_moved = true;
      for (int i = 0; i < static_cast<int>(store_guys.size()); ++i) {
        if (!BeamOneOpt(store_guys[i])) {
          all_moved = false;
          break;
        }
      }
      if (all_moved && cur_ans_val < old_ans_val - cEps) {
        changed = true;
        continue;
      }
      for (int guy = 0; guy < people; ++guy) {
        if (cur_ans[guy] == old_ans[guy]) {
          continue;
        }
        if (cur_ans[guy] != -1) {
          int cur_store = cur_ans[guy];
          stores[cur_store].guys.erase(guy);
          stores[cur_store].taken -= guys[guy].demand;
        }
        int old_store = old_ans[guy];
        stores[old_store].guys.insert(guy);
        stores[old_store].taken += guys[guy].demand;
        guys[guy].go_to = old_store;
        cur_ans[guy] = old_store;
      }
      stores[store].is_open = true;
      cur_ans_val = old_ans_val;
      cur_ans_counted = true;
    }
    return changed;
  }

  void BeamSearch() {
    cur_ans = best_ans;
    CountCurAns();
    SetStoresAndGuys(cur_ans);
    SetTabuBan();
    SetClosestStore();
    SetThirdDist();
    //BeamAddStore();
    //std::cout << "BeamAddStore Done " << cur_ans_val << std::endl;
    BeamChangingStore();
    //std::cout << "BeamChangingStore Done " << cur_ans_val << std::endl;
    //BeamRemStore();
    //std::cout << "BeamRemStore Done " << cur_ans_val << std::endl;
    BeamOneTwoOpt();
    //std::cout << "BeamOneTwoOpt Done " << cur_ans_val << std::endl;
    /*while (true) {
      bool changed = false;
      changed |= BeamOneTwoOpt();
      changed |= BeamChangingStore();
      changed |= BeamAddStore();
      changed |= BeamRemStore();
      std::cout << cur_ans_val << std::endl;
      if (!changed) {
        break;
      }
      SetThirdDist();
    }*/
    SetBetter();
  }

  db SetSolution(std::vector<int>& places, double* ans) {
    CleanStores();
    cur_ans.assign(people, -1);
    cur_ans_val = cInfty;
    cur_ans_counted = false;
    for (int i = 0; i < people; ++i) {
      guys[i].go_to = -1;
    }
    for (int i = 0; i < static_cast<int>(places.size()); ++i) {
      stores[places[i]].is_open = true;
    }
    std::vector<std::pair<int, int>> sure;
    std::vector<std::pair<int, std::vector<int>>> unsure;
    for (int i = 0; i < people; ++i) {
      std::vector<int> cond;
      for (int j = 0; j < static_cast<int>(places.size()); ++j) {
        if (ans[j * people + i] > cSimpEps) {
          cond.push_back(places[j]);
        }
      }
      if (cond.size() == 1) {
        sure.push_back({i, cond[0]});
      } else {
        unsure.push_back({i, cond});
      }
    }
    //std::cout << "Unsure are: " << unsure.size() << std::endl;
    for (int i = 0; i < static_cast<int>(sure.size()); ++i) {
      int guy = sure[i].first;
      int store = sure[i].second;
      if (!stores[store].can_take(guys[guy])) {
        throw std::logic_error("Sure is cringe!");
      }
      stores[store].Add(guy, guys[guy]);
      guys[guy].go_to = store;
      cur_ans[guy] = store;
    }
    std::vector<SPair1> candidates;
    for (int i = 0; i < static_cast<int>(unsure.size()); ++i) {
      int guy = unsure[i].first;
      for (int j = 0; j < static_cast<int>(places.size()); ++j) {
        int var = j * people + guy;
        if (ans[var] > cEps) {
          candidates.push_back({var, ans[var]});
        }
      }
    }
    std::sort(candidates.begin(), candidates.end(), Comp1);
    for (int i = static_cast<int>(candidates.size()) - 1; i >= 0; --i) {
      int var = candidates[i].first;
      int guy = var % people;
      int store = places[var / people];
      if (cur_ans[guy] == -1 && stores[store].can_take(guys[guy])) {
        stores[store].Add(guy, guys[guy]);
        guys[guy].go_to = store;
        cur_ans[guy] = store;
      }
    }
    int given_to_beam = 0;
    for (int i = 0; i < people; ++i) {
      if (cur_ans[i] == -1) {
        ++given_to_beam;
      }
    }
    //std::cout << "Given to Beam are: " << given_to_beam << std::endl;
    for (int i = 0; i < people; ++i) {
      if (cur_ans[i] == -1 && !BeamOneOpt(i)) {
        return cInfty;
      }
    }
    //SetBetter();
    //BeamOneTwoOpt();
    //CountCurAns();
    SetBetter();
    return cur_ans_val;
  }

  db LP(std::vector<bool>& mask) {
    std::vector<int> places;
    int bits = 0;
    for (int i = 0; i < mask.size(); ++i) {
      if (mask[i]) {
        ++bits;
        places.push_back(i);
      }
    }
    int vars = bits * people;
    ClpSimplex model;
    model.setLogLevel(0);
    model.resize(0, vars);
    for (int i = 0; i < people; ++i) {
      for (int j = 0; j < bits; ++j) {
        int place = j * people + i;
        model.setColumnLower(place, 0.0);
        model.setColumnUpper(place, 1.0);
        model.setObjectiveCoefficient(place, Dist(guys[i], stores[places[j]]));
      }
    }
    for (int i = 0; i < people; ++i) {
      std::vector<int> cols;
      std::vector<double> coef;
      for (int j = 0; j < bits; ++j) {
        cols.push_back(j * people + i);
        coef.push_back(1.0);
      }
      model.addRow(cols.size(), cols.data(), coef.data(), 1.0, 1.0);
    }
    for (int j = 0; j < bits; ++j) {
      std::vector<int> cols;
      std::vector<double> coef;
      for (int i = 0; i < people; ++i) {
        cols.push_back(j * people + i);
        coef.push_back(guys[i].demand);
      }
      model.addRow(cols.size(), cols.data(), coef.data(), -COIN_DBL_MAX,
                   stores[places[j]].cap);
    }
    model.initialSolve();
    if (model.isProvenPrimalInfeasible()) {
      return cInfty;
    }
    double* ans = model.primalColumnSolution();
    return SetSolution(places, ans);
  }

  bool ChangeOneOnMask(db& cur_met, std::vector<bool>& mask) {
    int counter = 0;
    bool changed = false;
    auto start = std::chrono::steady_clock::now();
    while (true) {
      auto end = std::chrono::steady_clock::now();
      auto duration = std::chrono::duration_cast<std::chrono::seconds>(end - start);
      if (duration.count() > 60) {
        break;
      }
      bool improved = false;
      for (int i = 0; i < shops; ++i) {
        auto end = std::chrono::steady_clock::now();
        auto duration = std::chrono::duration_cast<std::chrono::seconds>(end - start);
        if (duration.count() > 60) {
          break;
        }
        if (!mask[i]) {
          continue;
        }
        for (int j = 0; j < clos_store[i].size(); ++j) {
          int after = clos_store[i][j];
          if (mask[after]) {
            continue;
          }
          std::pair<int, int> change = {i, after};
          if (tabu_list.count(change) > 0 && tabu_list[change] > time) {
            continue;
          }
          mask[i] = false;
          mask[after] = true;
          ++counter;
          db new_met = LP(mask);
          if (new_met < cur_met - cEps) {
            //std::cout << "Changed on: " << counter << " " << new_met << std::endl;
            ++time;
            cur_met = new_met;
            improved = true;
            changed = true;
            break;
          } else {
            mask[i] = true;
            mask[after] = false;
            tabu_list[change] = time + tabu_ban;
          }
        }
      }
      if (!improved) {
        break;
      }
    }
    //std::cout << "Counter is:" << counter << " and in total is " << in_total << "\n";
    return changed;
  }

  bool ChangeTwoOnMask(db& cur_met, std::vector<bool>& mask) {
    int counter = 0;
    bool changed = false;
    auto start = std::chrono::steady_clock::now();
    while (true) {
      auto end = std::chrono::steady_clock::now();
      auto duration =
          std::chrono::duration_cast<std::chrono::seconds>(end - start);
      if (duration.count() > 60) {
        break;
      }
      bool improved = false;
      for (int i = 0; i < shops; ++i) {
        end = std::chrono::steady_clock::now();
        duration =
            std::chrono::duration_cast<std::chrono::seconds>(end - start);
        if (duration.count() > 60) {
          break;
        }
        int after1 = i;
        if (mask[after1]) {
          continue;
        }
        bool accepted = false;
        for (int j = 0; j < static_cast<int>(clos_store[after1].size()); ++j) {
          int before1 = clos_store[after1][j];
          if (!mask[before1]) {
            continue;
          }
          for (int k = 0; k < static_cast<int>(clos_store[before1].size()); ++k) {
            int after2 = clos_store[before1][k];
            if (mask[after2]) {
              continue;
            }
            for (int l = 0; l < static_cast<int>(clos_store[after2].size()); ++l) {
              int before2 = clos_store[after2][l];
              if (!mask[before2]) {
                continue;
              }
              mask[before1] = false;
              mask[before2] = false;
              mask[after1] = true;
              mask[after2] = true;
              db new_met = LP(mask);
              ++counter;
              if (new_met < cur_met - cEps) {
                //std::cout << "Changed via: " << counter << " " << new_met << std::endl;
                cur_met = new_met;
                improved = true;
                changed = true;
                accepted = true;
                break;
              } else {
                mask[before1] = true;
                mask[before2] = true;
                mask[after1] = false;
                mask[after2] = false;
              }
            }
            if (accepted) {
              break;
            }
          }
          if (accepted) {
            break;
          }
        }
      }
      if (!improved) {
        break;
      }
    }
    return changed;
  }

  void MaskLocalSearch() {
    cur_ans = best_ans;
    CountCurAns();
    SetStoresAndGuys(cur_ans);
    SetTabuBan();
    SetClosestStore();
    SetThirdDist();
    std::vector<bool> mask(shops, false);
    for (int i = 0; i < shops; ++i) {
      if (stores[i].is_open) {
        mask[i] = true;
      }
    }
    db cur_met = LP(mask);
    auto start = std::chrono::steady_clock::now();
    while (true) {
      bool changed = false;
      changed |= ChangeOneOnMask(cur_met, mask);
      auto end = std::chrono::steady_clock::now();
      auto duration = std::chrono::duration_cast<std::chrono::seconds>(end - start);
      if (duration.count() > 240) {
        break;
      }
      changed |= ChangeTwoOnMask(cur_met, mask);
      if (!changed) {
        break;
      }
      end = std::chrono::steady_clock::now();
      duration = std::chrono::duration_cast<std::chrono::seconds>(end - start);
      if (duration.count() > 240) {
        break;
      }
    }
  }

  void LPBasedBeam() {
    cur_ans = best_ans;
    CountCurAns();
    SetStoresAndGuys(cur_ans);
    SetTabuBan();
    SetClosestStore();
    SetThirdDist();
    std::vector<bool> mask(shops, false);
    for (int i = 0; i < shops; ++i) {
      mask[i] = stores[i].is_open;
    }
    std::unordered_set<std::vector<bool>> hash_map;
    hash_map.insert(mask);
    auto start = std::chrono::steady_clock::now();
    std::queue<std::vector<bool>> options;
    options.push(mask);
    std::mt19937 gen(67);
    std::uniform_int_distribution<int> dis(0, shops - 1);
    int counter = 0;
    db needed_cap = 0;
    for (int i = 0; i < people; ++i) {
      needed_cap += guys[i].demand;
    }
    while (true) {
      ++counter;
      auto end = std::chrono::steady_clock::now();
      auto duration = std::chrono::duration_cast<std::chrono::seconds>(end - start);
      if (duration.count() > 300) {
        break;
      }
      std::vector<std::vector<bool>> new_opt;
      std::vector<SPair1> metr;
      if (options.empty()) {
        break;
      }
      while (!options.empty()) {
        std::vector<bool> cur_mask = options.front();
        options.pop();
        int sons_found = 0;
        /*for (int i = 0; i < lp_beam_max_tries; ++i) {
          int pos = dis(gen);
          cur_mask[pos] = !cur_mask[pos];
          if (hash_map.count(cur_mask) == 1) {
            cur_mask[pos] = !cur_mask[pos];
            continue;
          }
          hash_map.insert(cur_mask);
          ++sons_found;
          new_opt.push_back(cur_mask);
          metr.push_back({metr.size(), LP(cur_mask)});
          cur_mask[pos] = !cur_mask[pos];
          if (sons_found >= lp_beam_sons) {
            break;
          }
        }*/
        db sum_dem = 0;
        for (int i = 0; i < shops; ++i) {
          if (cur_mask[i]) {
            sum_dem += stores[i].cap;
          }
        }
        for (int i = 0; i < shops; ++i) {
          if (cur_mask[i]) {
            sum_dem -= stores[i].cap;
          } else {
            sum_dem += stores[i].cap;
          }
          cur_mask[i] = !cur_mask[i];
          if ((sum_dem < needed_cap) || (hash_map.count(cur_mask) == 1)) {
            cur_mask[i] = !cur_mask[i];
            if (cur_mask[i]) {
              sum_dem += stores[i].cap;
            } else {
              sum_dem -= stores[i].cap;
            }
            continue;
          }
          hash_map.insert(cur_mask);
          ++sons_found;
          new_opt.push_back(cur_mask);
          metr.push_back({metr.size(), LP(cur_mask)});
          cur_mask[i] = !cur_mask[i];
          if (cur_mask[i]) {
            sum_dem += stores[i].cap;
          } else {
            sum_dem -= stores[i].cap;
          }
        }
      }
      std::sort(metr.begin(), metr.end(), Comp1);
      for (int i = 0; i < std::min(lp_beam_const, int(metr.size())); ++i) {
        options.push(new_opt[metr[i].first]);
      }
      if (counter % 1 == 0) {
        //std::cout << "Counter: " << counter << ", Metric: " << metr[0].second << std::endl;
      }
    }
    //std::cout << "Total counter: " << counter << std::endl;
  }

  void LP3Opt() {
    auto start = std::chrono::steady_clock::now();
    cur_ans = best_ans;
    CountCurAns();
    SetStoresAndGuys(cur_ans);
    std::vector<bool> mask(shops, false);
    std::vector<int> places;
    for (int i = 0; i < people; ++i) {
      mask[cur_ans[i]] = true;
    }
    for (int i = 0; i < shops; ++i) {
      if (mask[i]) {
        places.push_back(i);
      }
    }
    int bits = static_cast<int>(places.size());
    if (bits > 20) {
      return;
    }
    int vars = bits * people;
    for (int first = 0; first < bits; ++first) {
      for (int second = first + 1; second < bits; ++second) {
        auto end = std::chrono::steady_clock::now();
        auto duration = std::chrono::duration_cast<std::chrono::seconds>(end - start);
        if (duration.count() > 100) {
          break;
        }
        for (int third = second + 1; third < bits; ++third) {
          ClpSimplex model;
          model.setLogLevel(0);
          model.resize(0, vars);
          for (int i = 0; i < people; ++i) {
            int old_store = best_ans[i];
            for (int j = 0; j < bits; ++j) {
              int place = j * people + i;
              bool reconsider = j == first || j == second || j == third;
              double value = old_store == places[j] ? 1.0 : 0.0;
              model.setColumnLower(place, reconsider ? 0.0 : value);
              model.setColumnUpper(place, reconsider ? 1.0 : value);
              model.setObjectiveCoefficient(
                  place, Dist(guys[i], stores[places[j]]));
            }
          }
          for (int i = 0; i < people; ++i) {
            std::vector<int> cols;
            std::vector<double> coef;
            for (int j = 0; j < bits; ++j) {
              cols.push_back(j * people + i);
              coef.push_back(1.0);
            }
            model.addRow(cols.size(), cols.data(), coef.data(), 1.0, 1.0);
          }
          for (int j = 0; j < bits; ++j) {
            std::vector<int> cols;
            std::vector<double> coef;
            for (int i = 0; i < people; ++i) {
              cols.push_back(j * people + i);
              coef.push_back(guys[i].demand);
            }
            model.addRow(cols.size(), cols.data(), coef.data(),
                         -COIN_DBL_MAX, stores[places[j]].cap);
          }
          model.initialSolve();
          if (!model.isProvenPrimalInfeasible()) {
            double* ans = model.primalColumnSolution();
            SetSolution(places, ans);
          }
        }
      }
    }
  }

 public:

  FacilitySolver(std::string path, std::ostringstream& out) {
    InputData(path);
    shufle.reserve(people);
    for (int i = 0; i < people; ++i) {
      shufle.push_back(i);
    }
    cur_ans.resize(people, -1);
    best_ans.resize(people, -1);
    SetGuyPreference();
    ClosestEur();
    GeneralGreedy();
    
    if (shops < 250) {
      LocalSearch();
      BeamSearch();
      LPBasedBeam();
      LP3Opt();
    } else {
      LocalSearch();
      BeamSearch();
    }

    //Genetics();
    
    //Annealing1();
    //Annealing2();
    
    //MaskLocalSearch();
    
    
    OutputData(out);
  }
};

/*int main() {
  std::ostringstream out;
  FacilitySolver solve("data/fl_25_2", out);
  std::cout << out.str();
}*/
