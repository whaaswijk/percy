#pragma once

/* The Travis build environment has a different path to nauty. */
#ifdef TRAVIS_BUILD
#include <nauty.h>
#else
#include <nauty/nauty.h>
#endif

#include <vector>
#include <unordered_map>
#include <ostream>
#include <set>

using std::pair;
using std::unordered_map;

namespace percy
{

    class dag
    {
        private:
            int _nr_vars;
            int _nr_vertices;
            int* _js;
            int* _ks;

        public:

            dag() : _js(nullptr), _ks(nullptr)
            {
            }

            dag(dag&& dag)
            {
                _nr_vars = dag._nr_vars;
                _nr_vertices = dag._nr_vertices;

                _js = dag._js;
                _ks = dag._ks;

                dag._nr_vars = -1;
                dag._nr_vertices = -1;
                dag._js = nullptr;
                dag._ks = nullptr;
            }

            dag(const dag& dag) : _js(nullptr), _ks(nullptr)
            {
                reset(dag.nr_vars(), dag.nr_vertices());

                for (int i = 0; i < _nr_vertices; i++) {
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
                reset(dag.nr_vars(), dag.nr_vertices());
                for (int i = 0; i < _nr_vertices; i++) {
                    _js[i] = dag._js[i];
                    _ks[i] = dag._ks[i];
                }
                return *this;
            }

            bool operator==(const dag& g)
            {
                if (g._nr_vertices != _nr_vertices || g._nr_vars != _nr_vars) {
                    return false;
                }
                for (int i = 0; i < _nr_vertices; i++) {
                    if (_js[i] != g._js[i] || _ks[i] != g._ks[i]) {
                        return false;
                    }
                }
                return true;
            }

            bool operator!=(const dag& g) {
                return !(*this ==g);
            }

            void reset(int nr_vars, int nr_vertices)
            {
                _nr_vars = nr_vars;
                _nr_vertices = nr_vertices;
                if (_js != nullptr) {
                    delete[] _js;
                }
                _js = new int[nr_vertices];
                if (_ks != nullptr) {
                    delete[] _ks;
                }
                _ks = new int[nr_vertices];
            }

            void set_nr_vars(int nr_vars) { _nr_vars = nr_vars; }

            int nr_vertices() const { return _nr_vertices; }
            int nr_vars() const { return _nr_vars; }

            void set_vertex(int v_idx, int fanin1, int fanin2)
            {
                assert(v_idx < _nr_vertices);
                _js[v_idx] = fanin1;
                _ks[v_idx] = fanin2;
            }

            const pair<int,int> get_vertex(int v_idx) const
            {
                return std::make_pair(_js[v_idx], _ks[v_idx]);
            }

            // Swaps input variable pos with variable pos+1.
            void swap_adjacent_inplace(int pos)
            {
                for (int i = 0; i < _nr_vertices; i++) {
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

            void to_dot(std::ostream& o)
            {
                o << "graph{\n";
                o << "rankdir = BT\n";
                for (int i = 0; i < _nr_vars; i++) {
                    const auto idx = i + 1;
                    o << "x" << idx << " [shape=none,label=<x<sub>" << idx 
                        << "</sub>>];\n";
                }

                o << "node [shape=circle];\n";
                for (int i = 0; i < _nr_vertices; i++) {
                    const auto vertex = get_vertex(i);
                    const auto idx = _nr_vars + i + 1;
                    o << "x" << idx << " [label=<x<sub>" << idx 
                        << "</sub>>];\n";
                    
                    o << "x" << vertex.first+1 << " -- x" << idx << ";\n";
                    o << "x" << vertex.second+1 << " -- x" << idx << ";\n";
                }

                // Group inputs on same level.
                o << "{rank = same; ";
                for (int i = 0; i < _nr_vars; i++) {
                    o << "x" << i+1 << "; ";
                }
                o << "}\n";

                // Add invisible edges between PIs to enforce order.
                o << "edge[style=invisible];\n";
                for (int i = _nr_vars; i > 1; i--) {
                    o << "x" << i-1 << " -- x" << i << ";\n";
                }


                o << "}\n";
            }

            /*******************************************************************
                Uses the Nauty package to check for isomorphism beteen DAGs.
            *******************************************************************/
            bool
            is_isomorphic(const dag& g, int verbosity=0) const
            {
                const auto total_vertices = _nr_vars + _nr_vertices;
                assert(_nr_vertices == g.nr_vertices() && 
                        _nr_vars == g.nr_vars());

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
                for (int i = 0; i < _nr_vertices; i++) {
                    const auto vertex = get_vertex(i);
                    ADDONEARC(g1, vertex.first, _nr_vars+i, m);
                    ADDONEARC(g1, vertex.second, _nr_vars+i, m);
                }

                // Make the second graph
                DYNALLOC2(graph,g2,g2_sz,total_vertices,m,"malloc");
                EMPTYGRAPH(g2,m,total_vertices);
                for (int i = 0; i < _nr_vertices; i++) {
                    const auto& vertex = g.get_vertex(i);
                    ADDONEARC(g2, vertex.first, _nr_vars+i, m);
                    ADDONEARC(g2, vertex.second, _nr_vars+i, m);
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
                assert(_nr_vertices == g.nr_vertices() && 
                        _nr_vars == g.nr_vars());

                std::multiset<pair<int,int>> g1_vertices;
                std::multiset<pair<int,int>> g2_vertices;

                dag cpy(g);
                const auto& swaps = kitty::detail::swaps[_nr_vars - 2u];
                int swap_counter = 0;
                do {
                    g1_vertices.clear();
                    g2_vertices.clear();
                    for (int i = 0; i < _nr_vertices; i++) {
                        const auto& v1 = get_vertex(i);
                        const auto& v2 = cpy.get_vertex(i);
                        g1_vertices.insert(v1);
                        g2_vertices.insert(v2);
                    }

                    bool isomorphic = true;
                    for (int i = 0; i < _nr_vertices; i++) {
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

}
