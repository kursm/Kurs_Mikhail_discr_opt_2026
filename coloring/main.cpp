#include <algorithm>
#include <chrono>
#include <fstream>
#include <iostream>
#include <queue>
#include <random>
#include <set>
#include <sstream>
#include <stdexcept>
#include <string>
#include <tuple>
#include <unordered_set>
#include <vector>

struct VectorHasher {
 private:

  static std::vector<int> Coefs() {
    const int cNum = 1010;
    const int cMax = 50000;
    std::vector<int> ans;
    std::uniform_int_distribution<int> dist(1, cMax);
    std::mt19937 gen(std::random_device{}());
    for (int i = 0; i < cNum; ++i) {
      ans.push_back(dist(gen));
    }
    return ans;
  }

 public:

  long long prime = 999999937;
  std::vector<int> coefs;

  VectorHasher() {
    coefs = Coefs();
  }

  long long Hash(const std::vector<int>& vec) const {
    long long sum = 0;
    if (vec.size() > coefs.size()) {
      throw std::runtime_error("Not enough coefs for hasher!\n");
    }
    for (size_t i = 0; i < vec.size(); ++i) {
      sum = (sum + (vec[i] + 1) * coefs[i]) % prime;
    }
    return sum;
  }
};

const VectorHasher vhs;

struct ColoringSolver {
 public:
  struct Graph {

    struct Mex {

      private:
      std::vector<std::pair<int, int>> neib;
      std::vector<bool> taken;

      public:
      Mex(int n) {
        neib.resize(n + 2, std::pair<int, int>(0, 1));
        taken.resize(n + 2, false);
        for (int i = 1; i < n + 2; ++i) {
          neib[i] = std::pair<int, int>(i - 1, i + 1);
        }
      }

      int GetMex() {
        return neib[0].second;
      }

      void Rem(int num) {
        if (num == 0) {
          throw std::runtime_error("Do not give 0 to Mex!!!");
        }
        if (taken[num]) {
          return;
        }
        taken[num] = true;
        neib[neib[num].first].second = neib[num].second;
        neib[neib[num].second].first = neib[num].first;
      }
    };
    

    std::vector<std::vector<int>> edges;
    std::vector<std::vector<bool>> mat;
    std::vector<int> color;
    int v_num;
    int c_num;

    Graph () = default;

    Graph (int v, std::vector<std::pair<int, int>>& edg) {
      v_num = v;
      edges.resize(v_num, std::vector<int>());
      mat.resize(v_num, std::vector<bool>(v_num, false));
      for (size_t i = 0; i < edg.size(); ++i) {
        edges[edg[i].first].push_back(edg[i].second);
        edges[edg[i].second].push_back(edg[i].first);
        mat[edg[i].first][edg[i].second] = true;
        mat[edg[i].second][edg[i].first] = true;
      }
      color.resize(v_num, -1);
    }

    std::vector<int> SetColor(std::vector<int>& perm) {
      std::vector<int> rev_perm(v_num, 0);
      for (size_t i = 0; i < perm.size(); ++i) {
        rev_perm[perm[i]] = i;
      }
      std::vector<int> ans;
      for (int i = 0; i < v_num; ++i) {
        Mex col(v_num);
        for (size_t j = 0; j < edges[perm[i]].size(); ++j) {
          if (i > rev_perm[edges[perm[i]][j]]) {
            col.Rem(color[edges[perm[i]][j]]);
          }
        }
        color[perm[i]] = col.GetMex();
        if (color[perm[i]] - 1 >= ans.size()) {
          ans.push_back(0);
          if (color[perm[i]] - 1 >= ans.size()) {
            throw std::runtime_error("Technically impossible ans size!");
          }
        }
        ++ans[color[perm[i]] - 1];
      }
      c_num = ans.size();
      return ans;
    }
  };

  int vert_num;
  int best_known = 1E6;
  int random_iters = 5000;
  static inline long double a = 2;
  long double temp;
  long double temp_change = 0.9999;
  long double temp_delta = 0.995;
  long double temp_stop = 1E-8;
  Graph gr;
  std::vector<int> best_col;
  std::vector<int> best_distrib;
  std::vector<int> cur_distrib;
  std::vector<std::pair<int, int>> inp_edges;
  using Pair = std::pair<int, int>;

  void InpData(std::string& path) {
    std::ifstream input_file(path);
    int edg_num;
    input_file >> vert_num >> edg_num;
    inp_edges.resize(edg_num);
    for (int i = 0; i < edg_num; ++i) {
      input_file >> inp_edges[i].first >> inp_edges[i].second;
    }
  }

  void SetBetter() {
    if (best_known > gr.c_num) {
      best_known = gr.c_num;
      best_col = gr.color;
    }
  }

 private:

  static bool Comp(Pair ft, Pair sc) {
    return (ft.first > sc.first) ||
           ((ft.first == sc.first) && (ft.second < sc.second));
  }

 public:

  void SetRand(std::vector<int>& perm) {
    std::random_device rd;
    std::mt19937 gen(rd());
    std::shuffle(perm.begin(), perm.end(), gen);
  }

  std::vector<int> PermEur(std::vector<int> perm = {}) {
    const int cMaxIter = 100;
    if (perm.size() != vert_num) {
      perm.resize(vert_num);
      std::vector<Pair> deg(vert_num);
      for (int i = 0; i < vert_num; ++i) {
        deg[i] = Pair(gr.edges[i].size(), i);
      }
      std::sort(deg.begin(), deg.end(), Comp);
      for (int i = 0; i < vert_num; ++i) {
        perm[i] = deg[i].second;
      }
    }
    std::vector<int> past_dist = gr.SetColor(perm);
    std::vector<int> cur_col = gr.color;
    SetBetter();
    for (int i = 0; i < cMaxIter; ++i) {
      std::vector<Pair> for_sort(past_dist.size());
      for (int j = 0; j < past_dist.size(); ++j) {
        for_sort[j] = Pair(past_dist[j], j);
      }
      std::sort(for_sort.begin(), for_sort.end(), Comp);
      std::vector<int> col_rev(past_dist.size());
      for (int j = 0; j < past_dist.size(); ++j) {
        col_rev[for_sort[j].second] = j;
      }
      for (int j = 1; j < past_dist.size(); ++j) {
        for_sort[j].first += for_sort[j - 1].first;
      }
      for (int j = 0; j < vert_num; ++j) {
        perm[--for_sort[col_rev[cur_col[j] - 1]].first] = j;
      }
      std::vector<int> n_dist = gr.SetColor(perm);
      if (past_dist == n_dist) {
        break;
      }
      std::swap(past_dist, n_dist);
      cur_col = gr.color;
      SetBetter();
    }
    return perm;
  }

 private:
 
  static bool Comp2(Pair ft, Pair sc) {
    if ((ft.second > 0) && (sc.second > 0)) {
      return ft.first < sc.first;
    }
    if ((ft.second < 0) && (sc.second > 0)) {
      return (-ft.second) < sc.second;
    }
    if ((ft.second > 0) && (sc.second < 0)) {
      return ft.second <= (-sc.second);
    }
    if ((ft.second < 0) && (sc.second < 0)) {
      return (((-ft.second) < (-sc.second)) ||
              ((sc.second == ft.second) && (ft.first < sc.first)));
    }
    return true;
  }

 public:

  std::vector<int> PermLastPush(std::vector<int> perm = {}) {
    const int cMaxIter = 100;
    perm = PermEur(perm);
    int ver = perm.back();
    int ver_ind = int(perm.size()) - 1;
    for (int i = 0; i < cMaxIter; ++i) {
      int colors = gr.color[ver];
      std::vector<std::vector<int>> sp_col(colors);
      for (size_t j = 0; j < gr.edges[ver].size(); ++j) {
        if (gr.color[gr.edges[ver][j]] >= colors) {
          throw std::runtime_error("Logical assamption failed");
        }
        sp_col[gr.color[gr.edges[ver][j]]].push_back(gr.edges[ver][j]);
      }
      bool not_done = true;
      for (int j = 1; j < colors; ++j) {
        bool is_deletable = true;
        std::vector<Graph::Mex> free_col(sp_col[j].size(), Graph::Mex(colors));
        for (size_t k = 0; k < sp_col[j].size(); ++k) {
          for (size_t l = 0; l < gr.edges[sp_col[j][k]].size(); ++l) {
            free_col[k].Rem(gr.color[gr.edges[sp_col[j][k]][l]]);
          }
          free_col[k].Rem(j);
          if (free_col[k].GetMex() == colors + 1) {
            is_deletable = false;
            break;
          }
        }
        if (is_deletable) {
          not_done = false;
          for (size_t k = 0; k < sp_col[j].size(); ++k) {
            gr.color[sp_col[j][k]] *= -free_col[k].GetMex();
          }
          gr.color[ver] = -j;
          std::vector<Pair> for_sort(vert_num);
          for (int k = 0; k < vert_num; ++k) {
            for_sort[k] = Pair(k, gr.color[perm[k]]);
          }
          std::sort(for_sort.begin(), for_sort.end(), Comp2);
          std::vector<int> perm_n(perm.size());
          for (size_t k = 0; k < perm.size(); ++k) {
            perm_n[k] = perm[for_sort[k].first];
          }
          perm = PermEur(perm_n);
          ver = perm.back();
          ver_ind = int(perm.size()) - 1;
          break;
        }
      }
      if (not_done) {
        if (ver_ind != 0) {
          if (gr.color[perm[ver_ind]] == gr.color[perm[ver_ind - 1]]) {
            --ver_ind;
            ver = perm[ver_ind];
            continue;
          }
        }
        break;
      }
      if (i == cMaxIter - 1) {
        std::cout << "Not Enough!\n";
      }
    }
    return perm;
  }

  static bool LocalSearchComparator(std::vector<int>& distrib,
                                    std::vector<int>& distrib_other) {
    if (distrib.size() != distrib_other.size()) {
      return distrib.size() < distrib_other.size();
    }
    for (int i = int(distrib.size()) - 1; i > -1; --i) {
      if (distrib[i] != distrib_other[i]) {
        return distrib[i] < distrib_other[i];
      }
    }
    return false;
  }

  static bool LocalSearchComparator2(std::vector<int>& distrib,
                                    std::vector<int>& distrib_other) {
    if (distrib.size() != distrib_other.size()) {
      return distrib.size() < distrib_other.size();
    }
    long double value1 = 0;
    long double value2 = 0;
    for (int i = 0; i < distrib.size(); ++i) {
      long double pw = std::pow(static_cast<long double>(i), a);
      value1 += distrib[i] * pw;
      value2 += distrib_other[i] * pw;
    }
    return 1E-3 < value2 - value1;
  }

  std::vector<int> FindDistrib(std::vector<int>& perm) {
    return gr.SetColor(perm);
  }

 private:

  struct LSHeapEl {
    std::vector<int> distr;
    std::vector<int> perm;
    int reveal;

    LSHeapEl(std::vector<int> d, std::vector<int> p, int r)
      : distr(d),
        perm(p),
        reveal(r)
    {}
  };

  struct CustomLess {
    bool operator()(LSHeapEl& ft, LSHeapEl& sc) {
      if (ft.distr != sc.distr) {
        return LocalSearchComparator(ft.distr, sc.distr);
      }
      return ft.reveal < sc.reveal;
    }
  };

 public:

  std::vector<int> BeamSearch() {
    int cMaxDepth = 500;
    int cBeamConst = 150;
    int cBeamSmallTime = 2500;
    int cBeamSearchTime = 30;
    auto start = std::chrono::steady_clock::now();
    std::vector<int> perm = PermLastPush();
    if (best_distrib.empty()) {
      best_distrib = FindDistrib(perm);
    }
    std::unordered_set<long long> opened;
    int iter = 0;
    while (true) {
      ++iter;
      auto end = std::chrono::steady_clock::now();
      auto duration = std::chrono::duration_cast<std::chrono::seconds>(end - start);
      if (duration.count() > cBeamSearchTime) {
        break;
      }
      gr.SetColor(perm);
      std::vector<int> distrib = FindDistrib(perm);
      opened.insert(vhs.Hash(perm));
      std::priority_queue<LSHeapEl, std::vector<LSHeapEl>, CustomLess> que;
      for (int i = perm.size() - 1; i > -1; --i) {
        if (gr.color[perm[i]] != gr.color[perm.back()]) {
          break;
        }
        que.push(LSHeapEl(distrib, perm, i));
      }
      bool changed = false;
      auto start2 = std::chrono::steady_clock::now();
      for (int i = 0; i < cMaxDepth; ++i) {
        auto end2 = std::chrono::steady_clock::now();
        auto duration2 = std::chrono::duration_cast<std::chrono::milliseconds>(end2 - start2);
        if (duration2.count() > cBeamSmallTime) {
          break;
        }
        std::vector<LSHeapEl> for_rev;
        for (int j = 0; j < cBeamConst; ++j) {
          if (que.empty()) {
            break;
          }
          for_rev.push_back(que.top());
          que.pop();
        }
        que = std::priority_queue<LSHeapEl, std::vector<LSHeapEl>,
                                  CustomLess>();
        for (size_t j = 0; j < for_rev.size(); ++j) {
          std::vector<int> r_perm(for_rev[j].perm.size());
          for (int k = 0; k < r_perm.size(); ++k) {
            r_perm[for_rev[j].perm[k]] = k;
          }
          for (int k = 0;
               k < gr.edges[for_rev[j].perm[for_rev[j].reveal]].size(); ++k) {
            std::vector<int> n_perm = for_rev[j].perm;
            std::swap(n_perm[for_rev[j].reveal],
                      n_perm[r_perm[gr.edges[for_rev[j].perm[for_rev[j].reveal]][k]]]);
            long long hash = vhs.Hash(n_perm);
            /*if (opened.count(hash) == 1) {
              continue;
            } else {
              opened.insert(hash);
            }*/
            std::vector<int> n_dist = FindDistrib(n_perm);
            if (LocalSearchComparator(n_dist, best_distrib)) {
              best_distrib = n_dist;
              changed = true;
              PermLastPush(n_perm);
              std::swap(perm, n_perm);
              break;
            } else {
              que.push(LSHeapEl(n_dist, n_perm, for_rev[j].reveal));
              que.push(LSHeapEl(n_dist, n_perm,
                  r_perm[gr.edges[for_rev[j].perm[for_rev[j].reveal]][k]]));
            }
          }
          if (changed) {
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
    //std::cout << iter;
    return perm;
  }

  std::vector<int> SetColorFast(std::vector<int>& perm) {
    std::vector<int> class_sizes;
    int cur_color = 1;
    int color_start = 0;
    class_sizes.push_back(0);
    for (int i = 0; i < perm.size(); ++i) {
      int v = perm[i];
      bool can_use_cur = true;
      for (int j = color_start; j < i; ++j) {
        if (gr.mat[v][perm[j]]) {
          can_use_cur = false;
          break;
        }
      }
      if (!can_use_cur) {
        ++cur_color;
        color_start = i;
        class_sizes.push_back(0);
      }
      gr.color[v] = cur_color;
      ++class_sizes[cur_color - 1];
    }
    gr.c_num = cur_color;
    return class_sizes;
  }

  static bool MaxFirstComp(Pair ft, Pair sc) {
    return (ft.first > sc.first) ||
           ((ft.first == sc.first) && (ft.second < sc.second));
  }

  bool MaxFirst(std::vector<int>& perm) {
    std::vector<int> cur_dist = SetColorFast(perm);
    std::vector<Pair> cls;
    cls.reserve(cur_dist.size());
    int pos = 0;
    for (int i = 0; i < cur_dist.size(); ++i) {
      cls.push_back(Pair(cur_dist[i], pos));
      pos += cur_dist[i];
    }
    std::sort(cls.begin(), cls.end(), MaxFirstComp);
    std::vector<int> n_perm;
    n_perm.reserve(perm.size());
    for (int i = 0; i < cls.size(); ++i) {
      for (int j = 0; j < cls[i].first; ++j) {
        n_perm.push_back(perm[cls[i].second + j]);
      }
    }
    std::vector<int> n_dist = SetColorFast(n_perm);
    if (LocalSearchComparator(n_dist, cur_dist)) {
      std::swap(perm, n_perm);
      return true;
    }
    SetColorFast(perm);
    return false;
  }

  static bool MinFirstComp(Pair ft, Pair sc) {
    return (ft.first < sc.first) ||
           ((ft.first == sc.first) && (ft.second < sc.second));
  }

  bool MinFirst(std::vector<int>& perm) {
    std::vector<int> cur_dist = SetColorFast(perm);
    std::vector<Pair> cls;
    cls.reserve(cur_dist.size());
    int pos = 0;
    for (int i = 0; i < cur_dist.size(); ++i) {
      cls.push_back(Pair(cur_dist[i], pos));
      pos += cur_dist[i];
    }
    std::sort(cls.begin(), cls.end(), MinFirstComp);
    std::vector<int> n_perm;
    n_perm.reserve(perm.size());
    for (int i = 0; i < cls.size(); ++i) {
      for (int j = 0; j < cls[i].first; ++j) {
        n_perm.push_back(perm[cls[i].second + j]);
      }
    }
    std::vector<int> n_dist = SetColorFast(n_perm);
    if (LocalSearchComparator(n_dist, cur_dist)) {
      std::swap(perm, n_perm);
      return true;
    }
    SetColorFast(perm);
    return false;
  }

  bool SlowMaxMinFirst(std::vector<int>& perm, bool is_max = true) {
    std::vector<int> cur_dist = gr.SetColor(perm);
    std::vector<Pair> cls;
    cls.reserve(cur_dist.size());
    int pos = 0;
    for (int i = 0; i < cur_dist.size(); ++i) {
      cls.push_back(Pair(cur_dist[i], pos));
      pos += cur_dist[i];
    }
    if (is_max) {
      std::sort(cls.begin(), cls.end(), MaxFirstComp);
    } else {
      std::sort(cls.begin(), cls.end(), MinFirstComp);
    }
    std::vector<int> n_perm;
    n_perm.reserve(perm.size());
    for (int i = 0; i < cls.size(); ++i) {
      for (int j = 0; j < cls[i].first; ++j) {
        n_perm.push_back(perm[cls[i].second + j]);
      }
    }
    std::vector<int> n_dist = gr.SetColor(n_perm);
    if (LocalSearchComparator(n_dist, cur_dist)) {
      std::vector<std::vector<int>> color_ord(n_dist.size());
      for (int i = 0; i < n_perm.size(); ++i) {
        int v = n_perm[i];
        color_ord[gr.color[v] - 1].push_back(v);
      }
      std::vector<int> color_perm;
      color_perm.reserve(perm.size());
      for (int i = 0; i < color_ord.size(); ++i) {
        for (int j = 0; j < color_ord[i].size(); ++j) {
          color_perm.push_back(color_ord[i][j]);
        }
      }
      std::swap(perm, color_perm);
      return true;
    }
    gr.SetColor(perm);
    return false;
  }

  bool MinMaxApproach(std::vector<int>& perm) {
    bool changed_any = false;
    //while (true) {
      if (MaxFirst(perm)) {
        SetBetter();
        changed_any = true;
        //continue;
      }
      if (MinFirst(perm)) {
        SetBetter();
        changed_any = true;
        //continue;
      }
      if (SlowMaxMinFirst(perm, true)) {
        SetBetter();
        changed_any = true;
        //continue;
      }
      if (SlowMaxMinFirst(perm, false)) {
        SetBetter();
        changed_any = true;
        //continue;
      }
      //break;
    //}
    return changed_any;
  }

  bool RandomPerm(std::vector<int>& perm) {
    std::vector<int> cur_dist = gr.SetColor(perm);
    std::vector<std::vector<int>> color_ord(cur_dist.size());
    for (int i = 0; i < perm.size(); ++i) {
      int v = perm[i];
      color_ord[gr.color[v] - 1].push_back(v);
    }
    std::vector<int> color_ids;
    color_ids.reserve(color_ord.size());
    for (int i = 0; i < color_ord.size(); ++i) {
      color_ids.push_back(i);
    }
    std::random_device rd;
    std::mt19937 gen(rd());
    for (int it = 0; it < random_iters; ++it) {
      std::shuffle(color_ids.begin(), color_ids.end(), gen);
      std::vector<int> n_perm;
      n_perm.reserve(perm.size());
      for (int i = 0; i < color_ids.size(); ++i) {
        int cid = color_ids[i];
        for (int j = 0; j < color_ord[cid].size(); ++j) {
          n_perm.push_back(color_ord[cid][j]);
        }
      }
      std::vector<int> n_dist = gr.SetColor(n_perm);
      if (LocalSearchComparator(n_dist, cur_dist)) {
        std::vector<std::vector<int>> n_color_ord(n_dist.size());
        for (int i = 0; i < n_perm.size(); ++i) {
          int v = n_perm[i];
          n_color_ord[gr.color[v] - 1].push_back(v);
        }
        std::vector<int> color_perm;
        color_perm.reserve(perm.size());
        for (int i = 0; i < n_color_ord.size(); ++i) {
          for (int j = 0; j < n_color_ord[i].size(); ++j) {
            color_perm.push_back(n_color_ord[i][j]);
          }
        }
        std::swap(perm, color_perm);
        return true;
      }
    }
    gr.SetColor(perm);
    return false;
  }

  int ColorTwoClasses(std::vector<int>& perm, int beg1, int beg2, int size1,
                       int size2) {
    std::vector<int> class2;
    class2.reserve(size2);
    for (int i = 0; i < size2; ++i) {
      class2.push_back(perm[beg2 + i]);
    }
    std::vector<int> moved;
    std::vector<int> stay1;
    moved.reserve(size1);
    stay1.reserve(size1);
    for (int i = 0; i < size1; ++i) {
      int v = perm[beg1 + i];
      bool can_move = true;
      for (int j = 0; j < class2.size(); ++j) {
        if (gr.mat[v][class2[j]]) {
          can_move = false;
          break;
        }
      }
      if (can_move) {
        moved.push_back(v);
      } else {
        stay1.push_back(v);
      }
    }
    int moved_cnt = moved.size();
    int old_pop = std::max(size1, size2);
    int new_size1 = size1 - moved_cnt;
    int new_size2 = size2 + moved_cnt;
    int new_pop = std::max(new_size1, new_size2);
    if ((moved_cnt == 0) || (new_pop <= old_pop)) {
      return 0;
    }
    int color1 = gr.color[perm[beg1]];
    int color2 = gr.color[perm[beg2]];
    int pos = beg1;
    for (int i = 0; i < class2.size(); ++i) {
      perm[pos++] = class2[i];
    }
    for (int i = 0; i < moved.size(); ++i) {
      perm[pos++] = moved[i];
      gr.color[moved[i]] = color2;
    }
    for (int i = 0; i < stay1.size(); ++i) {
      perm[pos++] = stay1[i];
      gr.color[stay1[i]] = color1;
    }
    return moved_cnt;
  }

  bool SwapTwoClasses(std::vector<int>& perm) {
    bool changed_any = false;
    SlowMaxMinFirst(perm, true);
    std::vector<int> dist = gr.SetColor(perm);
    std::vector<std::vector<int>> color_ord(dist.size());
    for (int i = 0; i < perm.size(); ++i) {
      int v = perm[i];
      color_ord[gr.color[v] - 1].push_back(v);
    }
    std::vector<int> color_perm;
    color_perm.reserve(perm.size());
    for (int i = 0; i < color_ord.size(); ++i) {
      for (int j = 0; j < color_ord[i].size(); ++j) {
        color_perm.push_back(color_ord[i][j]);
      }
    }
    std::swap(perm, color_perm);
    gr.SetColor(perm);
    std::vector<int> starts;
    starts.reserve(gr.c_num + 1);
    starts.push_back(0);
    for (int i = 1; i < perm.size(); ++i) {
      if (gr.color[perm[i]] != gr.color[perm[i - 1]]) {
        starts.push_back(i);
      }
    }
    starts.push_back(perm.size());
    while (true) {
      bool changed_pass = false;
      for (int i = 0; i + 2 < starts.size(); ++i) {
        int beg1 = starts[i];
        int beg2 = starts[i + 1];
        int size1 = starts[i + 1] - starts[i];
        int size2 = starts[i + 2] - starts[i + 1];
        if ((size1 == 0) || (size2 == 0)) {
          continue;
        }
        int moved = ColorTwoClasses(perm, beg1, beg2, size1, size2);
        if (moved > 0) {
          changed_pass = true;
          changed_any = true;
          starts[i + 1] = beg1 + size2 + moved;
        }
      }
      if (!changed_pass) {
        break;
      }
    }
    if (changed_any) {
      gr.SetColor(perm);
      return true;
    }
    return false;
  }

  bool MakeColorTheLast(std::vector<int>& perm) {
    bool changed_any = false;
    SlowMaxMinFirst(perm, true);
    std::vector<int> cur_dist = gr.SetColor(perm);
    auto start = std::chrono::steady_clock::now();
    while (true) {
      bool changed_here = false;
      int colors = cur_dist.size();
      std::vector<int> base_color = gr.color;
      for (int col = 1; col <= colors; ++col) {
        std::vector<int> n_perm;
        n_perm.reserve(perm.size());
        for (int i = 0; i < perm.size(); ++i) {
          if (base_color[perm[i]] != col) {
            n_perm.push_back(perm[i]);
          }
        }
        for (int i = 0; i < perm.size(); ++i) {
          if (base_color[perm[i]] == col) {
            n_perm.push_back(perm[i]);
          }
        }
        SlowMaxMinFirst(n_perm, true);
        std::vector<int> n_dist = gr.SetColor(n_perm);
        if (LocalSearchComparator(n_dist, cur_dist)) {
          std::swap(perm, n_perm);
          std::swap(cur_dist, n_dist);
          changed_any = true;
          changed_here = true;
          break;
        }
      }
      if (!changed_here) {
        break;
      }
      auto end = std::chrono::steady_clock::now();
      auto duration = std::chrono::duration_cast<std::chrono::seconds>(end - start);
      if (duration.count() > 5) {
        break;
      }
    }
    gr.SetColor(perm);
    return changed_any;
  }

  void LocalSearch() {
    std::vector<int> perm = PermLastPush();
    SetColorFast(perm);
    SetBetter();
    //MinMaxApproach(perm);
    while (true) {
      bool changed_staticaly = false;
      if (MinMaxApproach(perm)) {
        SetBetter();
        changed_staticaly = true;
      }
      if (SwapTwoClasses(perm)) {
        SetBetter();
        changed_staticaly = true;
      }
      /*if (MakeColorTheLast(perm)) {
        SetBetter();
        changed_staticaly = true;
      }*/
      if (changed_staticaly) {
        continue;
      }
      if (RandomPerm(perm)) {
        SetBetter();
        continue;
      }
      break;
    }
    /*while(true) {
      if (MakeColorTheLast(perm)) {
        SetBetter();
        continue;
      }
      if (SwapTwoClasses(perm)) {
        SetBetter();
        continue;
      }
      break;
    }*/
  }

  void SetTemperature() {
    //long double temp = 1000;
    temp_change = 0.9999;
    temp_stop = 1E-5;
  }

  void MetricAnnealing() {
    SetTemperature();
    temp = 1000;
    if (best_col.size() != vert_num) {
      return;
    }
    gr.color = best_col;
    int max_col = 0;
    for (int i = 0; i < vert_num; ++i) {
      if (gr.color[i] > max_col) {
        max_col = gr.color[i];
      }
    }
    gr.c_num = max_col;
    std::vector<int> distrib(max_col, 0);
    for (int i = 0; i < vert_num; ++i) {
      ++distrib[gr.color[i] - 1];
    }
    gr.c_num = max_col;
    long double metric = 0;
    for (int i = 0; i < distrib.size(); ++i) {
      metric += distrib[i] * std::pow(static_cast<long double>(i), a);
    }
    //std::cout << "Metric is: " << metric / vert_num << "\n";
    temp = static_cast<long double>(1000) * metric *
           std::pow(static_cast<long double>(vert_num), 0.66);
    std::random_device rd;
    std::mt19937 gen(rd());
    std::uniform_int_distribution<int> vert_dist(0, vert_num - 1);
    std::uniform_real_distribution<long double> prob_dist(0.0, 1.0);
    int iter = 0;
    std::queue<long double> delta_queue;
    long double delta_sum = 0;
    while (temp > temp_stop) {
      int v = vert_dist(gen);
      int old_col = gr.color[v];
      std::set<int> free_colors;
      for (int col = 1; col <= max_col; ++col) {
        free_colors.insert(col);
      }
      for (int i = 0; i < gr.edges[v].size(); ++i) {
        free_colors.erase(gr.color[gr.edges[v][i]]);
      }
      std::vector<int> lower;
      std::vector<int> higher;
      for (std::set<int>::iterator it = free_colors.begin();
           it != free_colors.end(); ++it) {
        if (*it < old_col) {
          lower.push_back(*it);
        } else if (*it > old_col) {
          higher.push_back(*it);
        }
      }
      if (lower.empty() && higher.empty()) {
        temp *= temp_change;
        continue;
      }
      ++iter;
      int new_col = old_col;
      if (!lower.empty()) {
        std::uniform_int_distribution<int> pick(0, int(lower.size()) - 1);
        new_col = lower[pick(gen)];
      } else {
        std::uniform_int_distribution<int> pick(0, int(higher.size()) - 1);
        new_col = higher[pick(gen)];
      }
      int old_i = old_col - 1;
      int new_i = new_col - 1;
      long double delta = std::pow(static_cast<long double>(new_i), a) -
                          std::pow(static_cast<long double>(old_i), a);
      delta_queue.push(delta);
      delta_sum += delta;
      if (delta_queue.size() > 20) {
        delta_sum -= delta_queue.front();
        delta_queue.pop();
      }
      bool accept = false;
      /*if (iter % 10000 == 20) {
        long double delta_avg = delta_sum / delta_queue.size();
        std::cout << "Temp par: " << iter << " " << temp << " " << delta_avg << " "
                  << -delta_avg / temp << " " << std::exp(-delta_avg / temp) << "\n";
      }*/
      if (delta <= 0) {
        accept = true;
      } else {
        long double prob = std::exp(-delta / temp);
        accept = prob_dist(gen) < prob;
      }
      if (accept) {
        gr.color[v] = new_col;
        --distrib[old_i];
        ++distrib[new_i];
        metric += delta;
        if (distrib[old_i] == 0) {
          for (int u = 0; u < vert_num; ++u) {
            if (gr.color[u] > old_col) {
              --gr.color[u];
            }
          }
          distrib.erase(distrib.begin() + old_i);
          --max_col;
          metric = 0;
          for (int i = 0; i < distrib.size(); ++i) {
            metric += distrib[i] * std::pow(static_cast<long double>(i), a);
          }
          gr.c_num = max_col;
          SetBetter();
        }
      }
      temp *= temp_change;
    }
    //std::cout << "Iters done" << iter << '\n';
  }

  void LocalAndAnnealing() {
    auto start = std::chrono::steady_clock::now();
    std::vector<int> perm = PermLastPush();
    SetColorFast(perm);
    SetBetter();
    while (true) {
      bool changed_staticaly = false;
      if (MinMaxApproach(perm)) {
        SetBetter();
        changed_staticaly = true;
      }
      if (SwapTwoClasses(perm)) {
        SetBetter();
        changed_staticaly = true;
      }
      if (changed_staticaly) {
        continue;
      }
      if (RandomPerm(perm)) {
        SetBetter();
        continue;
      }
      break;
    }
    auto end = std::chrono::steady_clock::now();
    auto duration = std::chrono::duration_cast<std::chrono::seconds>(end - start);
    //std::cout << "First gone: " << duration.count() << "\n";
    int max_iter = 20; // 20
    for (int iters = 0; iters < max_iter; ++iters) {
      MetricAnnealing();
      int max_col = 0;
      for (int i = 0; i < vert_num; ++i) {
        if (gr.color[i] > max_col) {
          max_col = gr.color[i];
        }
      }
      std::vector<std::vector<int>> by_color(max_col + 1);
      for (int i = 0; i < vert_num; ++i) {
        by_color[gr.color[i]].push_back(i);
      }
      perm.clear();
      perm.reserve(vert_num);
      for (int col = 1; col <= max_col; ++col) {
        for (int j = 0; j < by_color[col].size(); ++j) {
          perm.push_back(by_color[col][j]);
        }
      }
      gr.SetColor(perm);
      SetBetter();
    }
    end = std::chrono::steady_clock::now();
    duration = std::chrono::duration_cast<std::chrono::seconds>(end - start);
    //std::cout << "Second gone: " << duration.count() << "\n";
    while (true) {
      bool changed_staticaly = false;
      if (MinMaxApproach(perm)) {
        SetBetter();
        changed_staticaly = true;
      }
      if (SwapTwoClasses(perm)) {
        SetBetter();
        changed_staticaly = true;
      }
      if (changed_staticaly) {
        continue;
      }
      if (RandomPerm(perm)) {
        SetBetter();
        continue;
      }
      break;
    }
    end = std::chrono::steady_clock::now();
    duration = std::chrono::duration_cast<std::chrono::seconds>(end - start);
    //std::cout << "Third gone: " << duration.count() << "\n";
  }

  void SetTemperature2() {
    temp = 1500;
    temp_change = 0.9999;
    temp_stop = 4E-4;
  }

  void LastRepushed(bool& removed_color, int max_col, long long conflicts) {
    if (removed_color) {
      return;
    }
    bool changed = true;
    while (changed) {
      changed = false;
      for (int v = 0; v < vert_num; ++v) {
        int old_col = gr.color[v];
        std::vector<int> cnt(max_col + 1, 0);
        for (int j = 0; j < gr.edges[v].size(); ++j) {
          ++cnt[gr.color[gr.edges[v][j]]];
        }
        int best_col = old_col;
        int best_conf = cnt[old_col];
        for (int c = 1; c < max_col; ++c) {
          if (cnt[c] < best_conf) {
            best_conf = cnt[c];
            best_col = c;
          }
        }
        if (best_col != old_col) {
          conflicts += (best_conf - cnt[old_col]);
          gr.color[v] = best_col;
          changed = true;
        }
      }
      if (conflicts == 0) {
        gr.c_num = max_col - 1;
        SetBetter();
        removed_color = true;
        return;
      }
    }
  }

  void IncorrecntessAnnealing() {
    while (true) {
      long long iter = 0;
      SetTemperature2();
      gr.color = best_col;
      int max_col = 0;
      for (int i = 0; i < vert_num; ++i) {
        if (gr.color[i] > max_col) {
          max_col = gr.color[i];
        }
      }
      std::vector<int> last_col_v;
      for (int i = 0; i < vert_num; ++i) {
        if (gr.color[i] == max_col) {
          last_col_v.push_back(i);
        }
      }
      long long conflicts = 0;
      for (int i = 0; i < last_col_v.size(); ++i) {
        int v = last_col_v[i];
        std::vector<int> cnt(max_col + 1, 0);
        for (int j = 0; j < gr.edges[v].size(); ++j) {
          ++cnt[gr.color[gr.edges[v][j]]];
        }
        int best_to = 1;
        int best_cnt = cnt[1];
        for (int c = 2; c < max_col; ++c) {
          if (cnt[c] < best_cnt) {
            best_cnt = cnt[c];
            best_to = c;
          }
        }
        conflicts += best_cnt;
        gr.color[v] = best_to;
      }
      if (conflicts == 0) {
        gr.c_num = max_col - 1;
        SetBetter();
        continue;
      }
      std::random_device rd;
      std::mt19937 gen(rd());
      std::uniform_int_distribution<int> vert_dist(0, vert_num - 1);
      std::uniform_real_distribution<long double> p01(0.0, 1.0);
      std::queue<long double> delta_queue;
      long double delta_sum = 0;
      bool removed_color = false;
      while (temp > temp_stop) {
        ++iter;
        int v = vert_dist(gen);
        int old_col = gr.color[v];
        std::vector<int> cnt(max_col + 1, 0);
        for (int j = 0; j < gr.edges[v].size(); ++j) {
          ++cnt[gr.color[gr.edges[v][j]]];
        }
        std::vector<int> free_colors;
        for (int c = 1; c < max_col; ++c) {
          if (cnt[c] == 0) {
            free_colors.push_back(c);
          }
        }
        if (!free_colors.empty()) {
          std::uniform_int_distribution<int> pick(0, int(free_colors.size()) - 1);
          int new_col = free_colors[pick(gen)];
          if (new_col != old_col) {
            conflicts -= cnt[old_col];
            gr.color[v] = new_col;
          }
        } else {
          std::uniform_int_distribution<int> pick(1, max_col - 1);
          int new_col = pick(gen);
          if (new_col != old_col) {
            long long delta = cnt[new_col] - cnt[old_col];
            delta_queue.push(delta);
            delta_sum += delta;
            if (delta_queue.size() > 20) {
              delta_sum -= delta_queue.front();
              delta_queue.pop();
            }
            bool accept = false;
            if (delta <= 0) {
              accept = true;
            } else {
              long double prob = std::exp(-static_cast<long double>(delta) / temp);
              accept = p01(gen) < prob;
            }
            if (accept) {
              gr.color[v] = new_col;
              conflicts += delta;
            }
          }
        }
        /*if (iter % 10000 == 20) {
          long double delta_avg = delta_sum / delta_queue.size();
          std::cout << "Temp par: " << iter << " " << temp << " " << delta_avg << " "
                    << -delta_avg / temp << " " << std::exp(-delta_avg / temp) << "\n";
        }*/
        if (conflicts == 0) {
          gr.c_num = max_col - 1;
          SetBetter();
          removed_color = true;
          break;
        }
        if (iter % 50 == 0) {
          temp *= temp_change;
        }
      }
      LastRepushed(removed_color, max_col, conflicts);
      //std::cout << "Iter is: " << iter << "\n";
      if (!removed_color) {
        break;
      }
      //std::cout << "Done\n";
    }
  }

  ColoringSolver (std::string path, std::ostringstream& out) {
    InpData(path);
    gr = Graph(vert_num, inp_edges);
    
    //BeamSearch();

    /*int times = 20; //20
    if (vert_num > 500) {
      times = 2;
    }
    for (int i = 0; i < times; ++i) {
      LocalSearch();
    }*/

    int times = 4;
    if (vert_num > 500) {
      times = 1;
    }
    for (int i = 0; i < times; ++i) {
      LocalAndAnnealing();
    }

    auto start = std::chrono::steady_clock::now();
    int incor_times = 20;
    for (int i = 0; i < incor_times; ++i) {
      IncorrecntessAnnealing();
    }
    auto end = std::chrono::steady_clock::now();
    auto duration = std::chrono::duration_cast<std::chrono::milliseconds>(end - start);
    //std::cout << "Time: " << double(duration.count())  << " milliseconds" << "\n";

    out << best_known << "\n";
    for (int i = 0; i < vert_num; ++i) {
      out << best_col[i] << " ";
    }
    out << "\n";
  }
};
