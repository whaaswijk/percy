#pragma once

#include <nauty.h>
#include <vector>
#include <unordered_map>
#include <ostream>
#include <set>
#include <array>

using std::pair;
using std::unordered_map;

namespace percy
{

    template<int NrFanin=2>
    class dag
    {
        public:
            using fanin = int;
            using vertex = std::array<fanin, NrFanin>;

        private:
            int nr_inputs;
            std::size_t nr_vertices;

            std::vector<std::array<fanin, NrFanin>> vertices;

            void 
            copy_dag(const dag& dag)
            {
                reset(dag.nr_inputs, dag.nr_vertices);
                vertices.resize(dag.get_nr_vertices());

                for (std::size_t i = 0; i < nr_vertices; i++) {
                    for (int j = 0; j < NrFanin; j++) {
                        vertices[i][j] = dag.vertices[i][j];
                    }
                }
            }

        public:
            dag() { }

            dag(int n, int v)
            {
                reset(n, v);
            }

            dag(dag&& dag)
            {
                nr_inputs = dag.nr_inputs;
                nr_vertices = dag.nr_vertices;

                vertices = std::move(dag.vertices);

                dag.nr_inputs = -1;
                dag.nr_vertices = -1;
            }

            dag(const dag& dag)
            {
                copy_dag(dag);
            }


            dag& operator=(const dag& dag) 
            {
                copy_dag(dag);
                return *this;
            }

            bool operator==(const dag& g)
            {
                if (g.nr_vertices != nr_vertices || g.nr_inputs != nr_inputs) {
                    return false;
                }
                for (int i = 0; i < nr_vertices; i++) {
                    for (int j = 0; j < NrFanin; j++) {
                        if (vertices[i][j] != g.vertices[i][j]) {
                            return false;
                        }
                    }
                }
                return true;
            }

            bool operator!=(const dag& g) {
                return !(*this ==g);
            }

            template<typename Fn>
            void 
            foreach_input(Fn&& fn)
            {
                for (auto i = 0; i < nr_inputs; i++) {
                    fn(i);
                }
            }

            template<typename Fn>
            void 
            foreach_vertex(Fn&& fn)
            {
                for (std::size_t i = 0; i < nr_vertices; i++) {
                    fn(i);
                }
            }

            template<typename Fn>
            void 
            foreach_fanin(vertex v, Fn&& fn)
            {
                for (auto i = 0; i < NrFanin; i++) {
                    fn(v[i]);
                }
            }

            void 
            reset(int n, int v)
            {
                nr_inputs = n;
                nr_vertices = v;
                vertices.resize(nr_vertices);

                for (int i = 0; i < nr_vertices; i++) {
                    for (int j = 0; j < NrFanin; j++) {
                        vertices[i][j] = -1;
                    }
                }
            }

            void set_nr_inputs(int n) { nr_inputs = n; }

            int get_nr_vertices() const { return nr_vertices; }
            int get_nr_inputs() const { return nr_inputs; }

            void 
            set_vertex(int v_idx, const fanin* const fanins)
            {
                assert(v_idx < nr_vertices);
                for (int i = 0; i < NrFanin; i++) {
                    vertices[v_idx][i] = fanins[i];
                }
            }

            void 
            set_vertex(int v_idx, const std::vector<int>& fanins)
            {
                assert(v_idx < nr_vertices);
                assert(fanins.size() == NrFanin);
                for (int i = 0; i < NrFanin; i++) {
                    vertices[v_idx][i] = fanins[i];
                }
            }

            vertex& get_vertex(int v_idx)
            {
                return vertices[v_idx];
            }

            
    };


    template<>
    class dag<2>
    {
        private:
            int nr_inputs;
            int nr_vertices;
            int* _js;
            int* _ks;

        public:
            using fanin = int;
            using vertex = std::pair<int,int>;

            dag() : _js(nullptr), _ks(nullptr)
            {
            }

            dag(dag&& dag)
            {
                nr_inputs = dag.nr_inputs;
                nr_vertices = dag.nr_vertices;

                _js = dag._js;
                _ks = dag._ks;

                dag.nr_inputs = -1;
                dag.nr_vertices = -1;
                dag._js = nullptr;
                dag._ks = nullptr;
            }

            dag(const dag& dag) : _js(nullptr), _ks(nullptr)
            {
                reset(dag.nr_inputs, dag.nr_vertices);

                for (int i = 0; i < nr_vertices; i++) {
                    _js[i] = dag._js[i];
                    _ks[i] = dag._ks[i];
                }
            }

            ~dag()
            {
                if (_js != nullptr) {
                    delete[] _js;
                }
                if (_ks != nullptr) {
                    delete[] _ks;
                }
            }

            dag& operator=(const dag& dag) 
            {
                reset(dag.nr_inputs, dag.nr_vertices);
                for (int i = 0; i < nr_vertices; i++) {
                    _js[i] = dag._js[i];
                    _ks[i] = dag._ks[i];
                }
                return *this;
            }

            bool operator==(const dag& g)
            {
                if (g.nr_vertices != nr_vertices || g.nr_inputs != nr_inputs) {
                    return false;
                }
                for (int i = 0; i < nr_vertices; i++) {
                    if (_js[i] != g._js[i] || _ks[i] != g._ks[i]) {
                        return false;
                    }
                }
                return true;
            }

            bool operator!=(const dag& g) {
                return !(*this == g);
            }

            void reset(int n, int v)
            {
                nr_inputs = n;
                nr_vertices = v;
                if (_js != nullptr) {
                    delete[] _js;
                }
                _js = new int[nr_vertices];
                if (_ks != nullptr) {
                    delete[] _ks;
                }
                _ks = new int[nr_vertices];
            }

            void set_nr_inputs(int n) { nr_inputs = n; }

            int get_nr_vertices() const { return nr_vertices; }
            int get_nr_inputs() const { return nr_inputs; }

            void set_vertex(int v_idx, fanin fanin1, fanin fanin2)
            {
                assert(v_idx < nr_vertices);
                _js[v_idx] = fanin1;
                _ks[v_idx] = fanin2;
            }

            const pair<int,int> get_vertex(int v_idx) const
            {
                return std::make_pair(_js[v_idx], _ks[v_idx]);
            }

            template<typename Fn>
            void 
            foreach_input(Fn&& fn)
            {
                for (auto i = 0; i < nr_inputs; i++) {
                    fn(i);
                }
            }

            template<typename Fn>
            void 
            foreach_vertex(Fn&& fn)
            {
                for (std::size_t i = 0; i < nr_vertices; i++) {
                    fn(i);
                }
            }

            template<typename Fn>
            void 
            foreach_fanin(vertex v, Fn&& fn)
            {
                fn(v.first);
                fn(v.second);
            }

            // Swaps input variable pos with variable pos+1.
            void swap_adjacent_inplace(int pos)
            {
                for (int i = 0; i < nr_vertices; i++) {
                    if (_js[i] == pos) {
                        _js[i] = pos+1;
                    } else if (_js[i] == (pos+1)) {
                        _js[i] = pos;
                    }
                    if (_ks[i] == pos) {
                        _ks[i] = pos+1;
                    } else if (_ks[i] == (pos+1)) {
                        _ks[i] = pos;
                    }
                }
            }

            /*******************************************************************
                Uses the Nauty package to check for isomorphism beteen DAGs.
            *******************************************************************/
            bool
            is_isomorphic(const dag& g, int verbosity=0) const
            {
                const auto total_vertices = nr_inputs + nr_vertices;
                assert(nr_vertices == g.nr_vertices && 
                        nr_inputs == g.nr_inputs);

                void (*adjacencies)(graph*, int*, int*, int, 
                        int, int, int*, int, boolean, int, int) = NULL;

                DYNALLSTAT(int,lab1,lab1_sz);
                DYNALLSTAT(int,lab2,lab2_sz);
                DYNALLSTAT(int,ptn,ptn_sz);
                DYNALLSTAT(int,orbits,orbits_sz);
                DYNALLSTAT(int,map,map_sz);
                DYNALLSTAT(graph,g1,g1_sz);
                DYNALLSTAT(graph,g2,g2_sz);
                DYNALLSTAT(graph,cg1,cg1_sz);
                DYNALLSTAT(graph,cg2,cg2_sz);
                DEFAULTOPTIONS_DIGRAPH(options);
                statsblk stats;

                int m = SETWORDSNEEDED(total_vertices);;

                options.getcanon = TRUE;

                DYNALLOC1(int,lab1,lab1_sz,total_vertices,"malloc");
                DYNALLOC1(int,lab2,lab2_sz,total_vertices,"malloc");
                DYNALLOC1(int,ptn,ptn_sz,total_vertices,"malloc");
                DYNALLOC1(int,orbits,orbits_sz,total_vertices,"malloc");
                DYNALLOC1(int,map,map_sz,total_vertices,"malloc");

                // Make the first graph
                DYNALLOC2(graph,g1,g1_sz,total_vertices,m,"malloc");
                EMPTYGRAPH(g1,m,total_vertices);
                for (int i = 0; i < nr_vertices; i++) {
                    const auto vertex = get_vertex(i);
                    ADDONEARC(g1, vertex.first, nr_inputs+i, m);
                    ADDONEARC(g1, vertex.second, nr_inputs+i, m);
                }

                // Make the second graph
                DYNALLOC2(graph,g2,g2_sz,total_vertices,m,"malloc");
                EMPTYGRAPH(g2,m,total_vertices);
                for (int i = 0; i < nr_vertices; i++) {
                    const auto& vertex = g.get_vertex(i);
                    ADDONEARC(g2, vertex.first, nr_inputs+i, m);
                    ADDONEARC(g2, vertex.second, nr_inputs+i, m);
                }

                // Create canonical graphs
                DYNALLOC2(graph,cg1,cg1_sz,total_vertices,m,"malloc");
                DYNALLOC2(graph,cg2,cg2_sz,total_vertices,m,"malloc");
                densenauty(g1,lab1,ptn,orbits,&options,&stats,m,total_vertices,cg1);
                densenauty(g2,lab2,ptn,orbits,&options,&stats,m,total_vertices,cg2);

                // Compare the canonical graphs to see if the two graphs are
                // isomorphic
                bool isomorphic = true;
                for (int k = 0; k < m*(size_t)total_vertices; k++) {
                    if (cg1[k] != cg2[k]) {
                        isomorphic = false;
                        break;;
                    }
                }
                if (isomorphic && verbosity) {
                    // Print the mapping between graphs for debugging purposes
                    for (int i = 0; i < total_vertices; ++i) {
                        map[lab1[i]] = lab2[i];
                    }
                    for (int i = 0; i < total_vertices; ++i) {
                        printf(" %d-%d",i,map[i]);
                    }
                    printf("\n");
                }

                return isomorphic;
            }


            /*******************************************************************
                Checks a restricted form of graph isomorphism: are two graphs
                isomorphic if we only allow for permutation of the inputs?
            *******************************************************************/
            bool
            is_perm_isomorphic(const dag& g, int verbosity=0) const
            {
                assert(nr_vertices == g.nr_vertices && 
                        nr_inputs == g.nr_inputs);

                std::multiset<pair<int,int>> g1_vertices;
                std::multiset<pair<int,int>> g2_vertices;

                dag cpy(g);
                const auto& swaps = kitty::detail::swaps[nr_inputs - 2u];
                int swap_counter = 0;
                do {
                    g1_vertices.clear();
                    g2_vertices.clear();
                    for (int i = 0; i < nr_vertices; i++) {
                        const auto& v1 = get_vertex(i);
                        const auto& v2 = cpy.get_vertex(i);
                        g1_vertices.insert(v1);
                        g2_vertices.insert(v2);
                    }

                    bool isomorphic = true;
                    for (int i = 0; i < nr_vertices; i++) {
                        const auto& v1 = get_vertex(i);
                        const auto& v2 = cpy.get_vertex(i);
                        if (g1_vertices.count(v1) != g2_vertices.count(v1)) {
                            isomorphic = false;
                            break;
                        }
                        if (g1_vertices.count(v2) != g2_vertices.count(v2)) {
                            isomorphic = false;
                            break;
                        }
                    }
                    if (isomorphic) {
                        return true;
                    }

                    if (swap_counter < swaps.size()) {
                        const auto pos = swaps[swap_counter];
                        cpy.swap_adjacent_inplace(pos);
                    }
                    swap_counter++;
                } while (swap_counter <= swaps.size());
                
                return false;
            }

    };

    using binary_dag = dag<2>;
    using ternary_dag = dag<3>;

}
