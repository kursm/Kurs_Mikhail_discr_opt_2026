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

struct FacilitySolver {
 private:
  struct Store;
  struct Guy;
  using db = long double;
  static inline const db cInfty = 1E10;
  int shops;
  int people;
  int cClosestEurTimes = 1;
  std::vector<Store> stores;
  std::vector<Guy> guys;
  std::vector<int> cur_ans;
  std::vector<int> best_ans;
  std::vector<std::vector<int>> guy_pref;
  std::set<int> store_open;
  db cur_ans_val = cInfty;
  db best_ans_val = cInfty;
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
    std::vector<int> shufle;
    shufle.reserve(people);
    for (int i = 0; i < people; ++i) {
      shufle.push_back(i);
    }
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
    while (true) {
      bool changed = false;
      for (int i = 0; i < people; ++i) {
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

  void OneTwoOpt() {
    if (best_ans_val == cInfty) {
      throw std::runtime_error("Solution for OneTwoOpt is not initialized");
    }
    cur_ans = best_ans;
    CountCurAns();
    SetStoresAndGuys(cur_ans);
    std::cout << "Done iterations: " << OneOpt() << "\n";
    SetBetter();
  }

 public:

  FacilitySolver(std::string path, std::ostringstream& out) {
    InputData(path);
    cur_ans.resize(people, -1);
    best_ans.resize(people, -1);
    SetGuyPreference();
    ClosestEur();
    OneTwoOpt();
    OutputData(out);
  }
};

/*int main() {
  std::ostringstream out;
  FacilitySolver solve("data/fl_25_2", out);
  std::cout << out.str();
}*/
