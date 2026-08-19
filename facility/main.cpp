#include <algorithm>
#include <cassert>
#include <chrono>
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

struct FacilitySolver {
 private:
  struct Store;
  struct Guy;
  using db = long double;
  using Ans = std::pair<std::vector<bool>, db>;
  static inline const db cInfty = 1E10;
  static inline const db cEps = 1E-3;
  int shops;
  int people;
  int cClosestEurTimes = 1;
  int pop_size = 8;
  int child_size = 8;
  int safe_zone = 0;
  int corv_attempts = 20;
  int gen_time = 180;
  int mut_pos = 10;
  std::vector<Store> stores;
  std::vector<Guy> guys;
  std::vector<int> cur_ans;
  std::vector<int> best_ans;
  std::vector<std::vector<int>> guy_pref;
  std::vector<std::vector<int>> hamming_dist;
  std::vector<std::vector<bool>> population;
  std::vector<db> pop_values;
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
    std::cout << "Total pop_size = " << pop_size << "\n";
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
      std::cout << "Reason to break is: " << average << "\n";
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
    std::cout << "Iterations number is: " << iterations << std::endl;
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

    Genetics();
    OutputData(out);
  }
};

/*int main() {
  std::ostringstream out;
  FacilitySolver solve("data/fl_25_2", out);
  std::cout << out.str();
}*/
