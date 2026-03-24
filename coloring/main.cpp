#include <algorithm>
#include <chrono>
#include <fstream>
#include <iostream>
#include <random>
#include <set>
#include <sstream>
#include <stdexcept>
#include <string>
#include <tuple>
#include <vector>

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
    std::vector<int> color;
    int v_num;
    int c_num;

    Graph () = default;

    Graph (int v, std::vector<std::pair<int, int>> edg) {
      v_num = v;
      edges.resize(v_num, std::vector<int>());
      for (size_t i = 0; i < edg.size(); ++i) {
        edges[edg[i].first].push_back(edg[i].second);
        edges[edg[i].second].push_back(edg[i].first);
      }
      color.resize(v_num, -1);
    }

    std::vector<int> SetColor(std::vector<int> perm) {
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
  std::vector<std::pair<int, int>> inp_edges;
  Graph gr;
  int best_known = 1E6;
  std::vector<int> best_col;

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
  using Pair = std::pair<int, int>;

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

  std::vector<int> PermLastPush() {
    const int cMaxIter = 100;
    std::vector<int> perm = PermEur();
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

  ColoringSolver (std::string path, std::ostringstream& out) {
    InpData(path);
    gr = Graph(vert_num, inp_edges);
    PermLastPush();
    out << best_known << "\n";
    for (int i = 0; i < vert_num; ++i) {
      out << best_col[i] << " ";
    }
    out << "\n";
  }
};