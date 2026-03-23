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

  std::vector<int> PermEur() {
    auto start = std::chrono::steady_clock::now();
    std::vector<int> perm(vert_num);
    for (int i = 0; i < vert_num; ++i) {
      perm[i] = i;
    }
    std::vector<int> past_dist = gr.SetColor(perm);
    std::vector<int> cur_col = gr.color;
    SetBetter();
    auto end = std::chrono::steady_clock::now();
    auto duration = std::chrono::duration_cast<std::chrono::seconds>(end - start);
    for (int iters = 0; iters < 10000; ++iters) {
      for (int i = 0; i < 100; ++i) {
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
      SetRand(perm);
    }
    return perm;
  }

  ColoringSolver (std::string path, std::ostringstream& out) {
    InpData(path);
    gr = Graph(vert_num, inp_edges);
    PermEur();
    out << best_known << "\n";
    for (int i = 0; i < vert_num; ++i) {
      out << best_col[i] << " ";
    }
    out << "\n";
  }
};