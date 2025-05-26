// https://github.com/ShahjalalShohag/code-library/blob/main/Graph%20Theory/Gomory%20Hu%20Tree.cpp

#include<bits/stdc++.h>
#define x first
#define y second

using namespace std;

typedef long long ll;
typedef pair<int, int> pii;

const int N = 3e5 + 9;
const ll inf = 1LL << 61;

struct Dinic {
  struct edge {
    int to, rev;
    ll flow, w;
    int id;
  };
  int n, s, t, mxid;
  vector<int> d, flow_through;
  vector<int> done;
  vector<vector<edge>> g;
  Dinic() {}
  Dinic(int _n) {
    n = _n + 10;
    mxid = 0;
    g.resize(n);
  }
  void add_edge(int u, int v, ll w, int id = -1) {
    edge a = {v, (int)g[v].size(), 0, w, id};
    edge b = {u, (int)g[u].size(), 0, w, -2};//for bidirectional edges cap(b) = w
    g[u].emplace_back(a);
    g[v].emplace_back(b);
    mxid = max(mxid, id);
  }
  bool bfs() {
    d.assign(n, -1);
    d[s] = 0;
    queue<int> q;
    q.push(s);
    while (!q.empty()) {
      int u = q.front();
      q.pop();
      for (auto &e : g[u]) {
        int v = e.to;
        if (d[v] == -1 && e.flow < e.w) d[v] = d[u] + 1, q.push(v);
      }
    }
    return d[t] != -1;
  }
  ll dfs(int u, ll flow) {
    if (u == t) return flow;
    for (int &i = done[u]; i < (int)g[u].size(); i++) {
      edge &e = g[u][i];
      if (e.w <= e.flow) continue;
      int v = e.to;
      if (d[v] == d[u] + 1) {
        ll nw = dfs(v, min(flow, e.w - e.flow));
        if (nw > 0) {
          e.flow += nw;
          g[v][e.rev].flow -= nw;
          return nw;
        }
      }
    }
    return 0;
  }
  ll max_flow(int _s, int _t) {
    s = _s;
    t = _t;
    ll flow = 0;
    while (bfs()) {
      done.assign(n, 0);
      while (ll nw = dfs(s, inf)) flow += nw;
    }
    flow_through.assign(mxid + 10, 0);
    for(int i = 0; i < n; i++) for(auto e : g[i]) if(e.id >= 0) flow_through[e.id] = e.flow;
    return flow;
  }
};

/*For a given weighted graph, int the Gomory-Hu tree the maximum flow 
between vertices u and v in the tree(i.e. minimum edge from u to v)
is equal to the maximum flow in the graph.*/
struct edge{
	int u, v;
	ll w;
};
// all nodes are from 1 to n
// returns edges of the gomory hu tree
vector<edge> gomory_hu_tree(int n, vector<edge> &ed) {
	vector<edge> ans;
	vector<int> par(n + 1, 1);
	for (int i = 2; i <= n; i++) {
    Dinic F(n + 1);
    for (auto &e : ed) F.add_edge(e.u, e.v, e.w);
		int s = i, t = par[i];
		ans.push_back({s, t, F.max_flow(s, t)});
		for (int j = i + 1; j <= n; j++) {
			if (F.d[j] != -1 and par[j] == par[i]) {
				par[j] = i;
			}
		}
	}
	return ans;
}

struct dsu {
	vector<int> par, rank, size;
	int c;
	dsu(int n) : par(n + 1), rank(n + 1, 0), size(n + 1, 1), c(n) {
		for (int i = 1; i <= n; ++i) par[i] = i;
	}
	int find(int i) {
		return (par[i] == i ? i : (par[i] = find(par[i])));
	}
	bool same(int i, int j) {
		return find(i) == find(j);
	}
	int get_size(int i) {
		return size[find(i)];
	}
	int count() {
		return c;
	}
	int merge(int i, int j) {
		if ((i = find(i)) == (j = find(j))) return -1;
		else --c;
		if (rank[i] > rank[j]) swap(i, j);
		par[i] = j;
		size[j] += size[i];
		if (rank[i] == rank[j]) rank[j]++;
		return j;
	}
};

struct Component {
  vector<int> nodes;
  vector<edge> edges;
  double modularity;
  int mincut;
  int minsize_after_mincut;
  pii optcut;

  int size() const {
    return nodes.size();
  }

  struct cmp {
    bool operator()(Component &i, Component &j) {
      if(i.mincut != j.mincut) return i.mincut > j.mincut;
      return i.minsize_after_mincut < j.minsize_after_mincut;
    }
  };
};
typedef pair<Component, Component> pcc;

struct Data {
  vector<Component> ground_truth;
  string network_path;
  string community_path;
  int num_comp;

  Data(string network_path, string community_path, int num_comp) : network_path(network_path), community_path(community_path), num_comp(num_comp) {
    ground_truth.resize(num_comp+1);
  }

  vector<vector<pii>> read(int n, int &m) {
    m = 0;
    vector<vector<pii>> adj(n+1);
    int u, v;

    ifstream network(network_path);
    while(network >> u >> v) {
      adj[u].push_back({v, 1});
      adj[v].push_back({u, 1});
      m++;
    }
    network.close();

    ifstream community(community_path);
    while(community >> u >> v) ground_truth[v].nodes.push_back(u);
    community.close();
    sort(ground_truth[1].nodes.begin(), ground_truth[1].nodes.end());
    sort(ground_truth[2].nodes.begin(), ground_truth[2].nodes.end());

    return adj;
  }

  void add_edges2gt(Component &comp, vector<vector<pii>> &adj) {
    for(int cur : comp.nodes)
    for(auto &it : adj[cur]) {
      int nxt = it.x;
      if(nxt < cur) continue;
      if(find(comp.nodes.begin(), comp.nodes.end(), nxt) != comp.nodes.end())
        comp.edges.push_back({cur, nxt, it.y});
    }
  }

  void add_edges2gt_all(vector<vector<pii>> &adj) {
    for(int i = 1; i <= num_comp; ++i)
      add_edges2gt(ground_truth[i], adj);
  }
};

struct Clustering {
  int n, m;
  vector<int> deg;
  vector<Component> cc;
  priority_queue<Component, vector<Component>, Component::cmp> pq;
  vector<Component> clusters;

  Clustering(int n, int m, vector<vector<pii>> &adj) : n(n), m(m) {
    deg.resize(n+1);
    for(int i = 1; i <= n; ++i) deg[i] = adj[i].size();
  }

  void find_connected_component(int cur, vector<int> &nodes, vector<bool> &visited, vector<vector<pii>> &adj) {
    visited[cur] = 1;
    nodes.push_back(cur);
    for(pii &it : adj[cur]) {
      if(visited[it.x]) continue;
      find_connected_component(it.x, nodes, visited, adj);
    }
  }

  void find_all_connected_component(vector<vector<pii>> &adj) {
    vector<bool> visited(n+1, 0);
    Component comp;
    for(int i = 1; i <= n; ++i) {
      if(visited[i]) continue;
      comp.nodes.clear();
      comp.edges.clear();
      find_connected_component(i, comp.nodes, visited, adj);
      sort(comp.nodes.begin(), comp.nodes.end());
      for(int cur : comp.nodes)
      for(pii &it : adj[cur]) {
        if(it.x < cur) continue;
        comp.edges.push_back({cur, it.x, it.y});
      }
      cc.push_back(comp);
    }
  }

  int compute_size(int cur, vector<bool> &visited, edge &cut, vector<vector<int>> &adj) {
    visited[cur] = 1;
    int ret = 1;
    for(int it : adj[cur]) {
      if(visited[it]) continue;
      if(cur == cut.u && it == cut.v) continue;
      if(cur == cut.v && it == cut.u) continue;
      ret += compute_size(it, visited, cut, adj);
    }
    return ret;
  }

  void find_optcut(Component &comp) {
    int sz = comp.size();

    unordered_map<int, int> idx, iidx;
    for(int i = 0; i < sz; ++i) {
      idx[comp.nodes[i]] = i+1;
      iidx[i+1] = comp.nodes[i];
    }
    vector<edge> ed;
    for(auto &it : comp.edges) ed.push_back({idx[it.u], idx[it.v], it.w});

    auto gh_tree = gomory_hu_tree(sz, ed);
    ll mincut = inf;
    for(auto &it : gh_tree) mincut = min(mincut, it.w);
    comp.mincut = mincut;

    vector<vector<int>> adj(sz+1);
    for(auto &it : gh_tree) {
      adj[it.u].push_back(it.v);
      adj[it.v].push_back(it.u);
    }

    int minsize = 0, u, v;
    for(auto &it : gh_tree) {
      if(it.w != mincut) continue;

      vector<bool> visited(sz+1, 0);
      int szu = compute_size(it.u, visited, it, adj);
      int szv = sz-szu;
      int mnsz = min(szu, szv);
      if(mnsz > minsize) {
        minsize = mnsz;
        u = it.u;
        v = it.v;
      }
    }
    comp.minsize_after_mincut = minsize;

    u = iidx[u];
    v = iidx[v];
    if(u > v) swap(u, v);
    comp.optcut = {u, v};
  }

  void find_splited_component(int cur, unordered_map<int, int> &iidx, vector<int> &nodes, vector<bool> &visited, vector<vector<pii>> &adj) {
    visited[cur] = 1;
    nodes.push_back(iidx[cur]);
    for(pii &it : adj[cur]) {
      if(visited[it.x]) continue;
      find_splited_component(it.x, iidx, nodes, visited, adj);
    }
  }

  pcc split_component(Component &comp) {
    int sz = comp.size();

    unordered_map<int, int> idx, iidx;
    for(int i = 0; i < sz; ++i) {
      idx[comp.nodes[i]] = i+1;
      iidx[i+1] = comp.nodes[i];
    }

    int u = idx[comp.optcut.x], v = idx[comp.optcut.y];
    vector<edge> ed;
    vector<vector<pii>> adj2(sz+1);
    for(auto &it : comp.edges) {
      ed.push_back({idx[it.u], idx[it.v], it.w});
      adj2[idx[it.u]].push_back({idx[it.v], it.w});
      adj2[idx[it.v]].push_back({idx[it.u], it.w});
    }

    auto gh_tree = gomory_hu_tree(sz, ed);
    vector<vector<pii>> adj(sz+1);
    for(auto &it : gh_tree) {
      if(it.u == u && it.v == v) continue;
      if(it.u == v && it.v == u) continue;
      adj[it.u].push_back({it.v, it.w});
      adj[it.v].push_back({it.u, it.w});
    }

    Component comp1, comp2;
    vector<bool> visited(sz+1, 0);
    find_splited_component(u, iidx, comp1.nodes, visited, adj);
    find_splited_component(v, iidx, comp2.nodes, visited, adj);
    sort(comp1.nodes.begin(), comp1.nodes.end());
    sort(comp2.nodes.begin(), comp2.nodes.end());

    for(int cur : comp1.nodes)
    for(auto &it : adj2[idx[cur]]) {
      int nxt = iidx[it.x];
      if(nxt < cur) continue;
      if(find(comp1.nodes.begin(), comp1.nodes.end(), nxt) != comp1.nodes.end())
        comp1.edges.push_back({cur, nxt, it.y});
    }
    for(int cur : comp2.nodes)
    for(auto &it : adj2[idx[cur]]) {
      int nxt = iidx[it.x];
      if(nxt < cur) continue;
      if(find(comp2.nodes.begin(), comp2.nodes.end(), nxt) != comp2.nodes.end())
        comp2.edges.push_back({cur, nxt, it.y});
    }

    return {comp1, comp2};
  }

  double compute_modularity(Component &comp) {
    int intra_conn = comp.edges.size();
    int deg_sum = 0;

    for(int it : comp.nodes) deg_sum += deg[it];
    comp.modularity = double(intra_conn)/m - pow(deg_sum/2.0/m, 2);
    return comp.modularity;
  }

  double compute_all_modularity() {
    double ret = 0;
    for(auto &it : clusters)
      ret += compute_modularity(it);
    return ret;
  }

  double modularity_threshold(int size) {
    return 0.03 + 0.05/sqrt(size);
  }

  void clustering() {
    for(auto &comp : cc) {
      if(comp.size() == 1) continue;

      compute_modularity(comp);
      if(comp.modularity >= modularity_threshold(comp.size())) clusters.push_back(comp);
      else {
        find_optcut(comp);
        pq.push(comp);
      }
    }

    while(!pq.empty()) {
      Component comp = pq.top();
      pq.pop();

      pcc splited_comp = split_component(comp);
      for(auto it : {splited_comp.x, splited_comp.y}) {
        if(it.size() == 1) continue;
        
        compute_modularity(it);
        if(it.modularity >= modularity_threshold(it.size())) clusters.push_back(it);
        else {
          find_optcut(it);
          pq.push(it);
        }
      }
    }
  }
};

string fill50(string str) {
  int len = str.length();
  int diff = 50-len;
  while(diff--) str.push_back(' ');
  return str;
}

int main() {
	int dolphin_n = 62, dolphin_m, dolphin_gt_num_comp = 2;
  Data dolphin("CS-DM/dolphin/network.dat", "CS-DM/dolphin/community.dat", dolphin_gt_num_comp);
	auto dolphin_adj = dolphin.read(dolphin_n, dolphin_m);
  dolphin.add_edges2gt_all(dolphin_adj);
  
  Clustering dolphin_gt(dolphin_n, dolphin_m, dolphin_adj);
  for(int i = 1; i <= dolphin_gt_num_comp; ++i)
    dolphin_gt.clusters.push_back(dolphin.ground_truth[i]);
  double dolphin_gt_modularity = dolphin_gt.compute_all_modularity();

  Clustering dolphin_exp(dolphin_n, dolphin_m, dolphin_adj);
  dolphin_exp.find_all_connected_component(dolphin_adj);
  dolphin_exp.clustering();
  double dolphin_exp_modularity = 0;
  for(auto &it : dolphin_exp.clusters)
    dolphin_exp_modularity += it.modularity;

  string dolphin_gt_num_comp_str = fill50("dolphin ground truth # components:");
  string dolphin_exp_num_comp_str = fill50("dolphin experiments # components:");
  string dolphin_gt_modularity_str = fill50("dolphin ground truth modularity:");
  string dolphin_exp_modularity_str = fill50("dolphin experiments modularity:");
  cout << dolphin_gt_num_comp_str << dolphin_gt_num_comp << '\n';
  cout << dolphin_exp_num_comp_str << dolphin_exp.clusters.size() << '\n';
  cout << dolphin_gt_modularity_str << dolphin_gt_modularity << '\n';
  cout << dolphin_exp_modularity_str << dolphin_exp_modularity << '\n';
  cout << "\n\n";


  int football_n = 115, football_m, football_gt_num_comp = 12;
  Data football("CS-DM/football/network.dat", "CS-DM/football/community.dat", football_gt_num_comp);
	auto football_adj = football.read(football_n, football_m);
  football.add_edges2gt_all(football_adj);
  
  Clustering football_gt(football_n, football_m, football_adj);
  for(int i = 1; i <= football_gt_num_comp; ++i)
    football_gt.clusters.push_back(football.ground_truth[i]);
  double football_gt_modularity = football_gt.compute_all_modularity();

  Clustering football_exp(football_n, football_m, football_adj);
  football_exp.find_all_connected_component(football_adj);
  football_exp.clustering();
  double football_exp_modularity = 0;
  for(auto &it : football_exp.clusters)
    football_exp_modularity += it.modularity;

  string football_gt_num_comp_str = fill50("football ground truth # components:");
  string football_exp_num_comp_str = fill50("football experiments # components:");
  string football_gt_modularity_str = fill50("football ground truth modularity:");
  string football_exp_modularity_str = fill50("football experiments modularity:");
  cout << football_gt_num_comp_str << football_gt_num_comp << '\n';
  cout << football_exp_num_comp_str << football_exp.clusters.size() << '\n';
  cout << football_gt_modularity_str << football_gt_modularity << '\n';
  cout << football_exp_modularity_str << football_exp_modularity << '\n';
  cout << "\n\n";


  int karate_n = 34, karate_m, karate_gt_num_comp = 2;
  Data karate("CS-DM/karate/network.dat", "CS-DM/karate/community.dat", karate_gt_num_comp);
	auto karate_adj = karate.read(karate_n, karate_m);
  karate.add_edges2gt_all(karate_adj);
  
  Clustering karate_gt(karate_n, karate_m, karate_adj);
  for(int i = 1; i <= karate_gt_num_comp; ++i)
    karate_gt.clusters.push_back(karate.ground_truth[i]);
  double karate_gt_modularity = karate_gt.compute_all_modularity();

  Clustering karate_exp(karate_n, karate_m, karate_adj);
  karate_exp.find_all_connected_component(karate_adj);
  karate_exp.clustering();
  double karate_exp_modularity = 0;
  for(auto &it : karate_exp.clusters)
    karate_exp_modularity += it.modularity;

  string karate_gt_num_comp_str = fill50("karate ground truth # components:");
  string karate_exp_num_comp_str = fill50("karate experiments # components:");
  string karate_gt_modularity_str = fill50("karate ground truth modularity:");
  string karate_exp_modularity_str = fill50("karate experiments modularity:");
  cout << karate_gt_num_comp_str << karate_gt_num_comp << '\n';
  cout << karate_exp_num_comp_str << karate_exp.clusters.size() << '\n';
  cout << karate_gt_modularity_str << karate_gt_modularity << '\n';
  cout << karate_exp_modularity_str << karate_exp_modularity << '\n';
  cout << "\n\n";


  int polblogs_n = 1224, polblogs_m, polblogs_gt_num_comp = 2;
  Data polblogs("CS-DM/polblogs/network.dat", "CS-DM/polblogs/community.dat", polblogs_gt_num_comp);
	auto polblogs_adj = polblogs.read(polblogs_n, polblogs_m);
  polblogs.add_edges2gt_all(polblogs_adj);
  
  Clustering polblogs_gt(polblogs_n, polblogs_m, polblogs_adj);
  for(int i = 1; i <= dolphin_gt_num_comp; ++i)
    polblogs_gt.clusters.push_back(polblogs.ground_truth[i]);
  double polblogs_gt_modularity = polblogs_gt.compute_all_modularity();

  Clustering polblogs_exp(polblogs_n, polblogs_m, polblogs_adj);
  polblogs_exp.find_all_connected_component(polblogs_adj);
  polblogs_exp.clustering();
  double polblogs_exp_modularity = 0;
  for(auto &it : polblogs_exp.clusters)
    polblogs_exp_modularity += it.modularity;

  string polblogs_gt_num_comp_str = fill50("polblogs ground truth # components:");
  string polblogs_exp_num_comp_str = fill50("polblogs experiments # components:");
  string polblogs_gt_modularity_str = fill50("polblogs ground truth modularity:");
  string polblogs_exp_modularity_str = fill50("polblogs experiments modularity:");
  cout << polblogs_gt_num_comp_str << polblogs_gt_num_comp << '\n';
  cout << polblogs_exp_num_comp_str << polblogs_exp.clusters.size() << '\n';
  cout << polblogs_gt_modularity_str << polblogs_gt_modularity << '\n';
  cout << polblogs_exp_modularity_str << polblogs_exp_modularity << '\n';

	return 0;
}