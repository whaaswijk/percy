#pragma once

#ifndef DISABLE_NAUTY
#include <nauty.h>
#endif
#include <vector>
#include <ostream>
#include <set>

namespace percy
{
    /// Convention: the zero fanin keeps a node's fanin "free". This fanin will not
    /// be connected to any of the other nodes in the partial DAG but rather may
    /// be connected to any one of the PIs.
    const int FANIN_PI = 0;

    class partial_dag
    {
        private:
            int fanin; /// The in-degree of vertices in the DAG
            std::vector<std::vector<int>> vertices;

        public:
            partial_dag() : fanin(0) { }

            partial_dag(int fanin, int nr_vertices = 0)
            {
                reset(fanin, nr_vertices);
            }

            partial_dag(const partial_dag& dag)
            {
                fanin = dag.fanin;
                vertices = dag.vertices;
            }

            partial_dag(partial_dag&& dag)
            {
                fanin = dag.fanin;
                vertices = std::move(dag.vertices);
            }

            template<typename Fn>
            void 
            foreach_vertex(Fn&& fn) const
            {
                for (std::size_t i = 0; i < nr_vertices(); i++) {
                    fn(vertices[i], i);
                }
            }

            template<typename Fn>
            void 
            foreach_fanin(std::vector<int>& v, Fn&& fn) const
            {
                for (auto i = 0; i < fanin; i++) {
                    fn(v[i], i);
                }
            }

            void 
            reset(int fanin, int nr_vertices)
            {
                this->fanin = fanin;
                vertices.resize(nr_vertices);
                for (auto& vertex : vertices) {
                    vertex.resize(fanin);
                }
            }

            void 
            set_vertex(int v_idx, const std::vector<int>& const fanins)
            {
                assert(v_idx < nr_vertices());
                assert(fanins.size() == fanin);
                for (int i = 0; i < fanin; i++) {
                    vertices[v_idx][i] = fanins[i];
                }
            }

            void
            set_vertex(int v_idx, int fi1, int fi2)
            {
                assert(v_idx < nr_vertices());
                vertices[v_idx][0] = fi1;
                vertices[v_idx][1] = fi2;
            }

            void 
            add_vertex(const std::vector<int>& const fanins)
            {
                assert(fanins.size() == fanin);
                vertices.push_back(fanins);
            }

            const std::vector<int>& 
            get_vertex(int v_idx) const
            {
                return vertices[v_idx];
            }

            int nr_vertices() const
            {
                return vertices.size();
            }

            
    };

    /***************************************************************************
        Converts a floating dag to the graphviz dot format and writes it to the
        specified output stream.
    ***************************************************************************/
    void 
    to_dot(const partial_dag& dag, std::ostream& o)
    {
        o << "graph{\n";

        o << "node [shape=circle];\n";
        dag.foreach_vertex([&dag, &o] (auto v, int v_idx) {
            const auto dot_idx = v_idx + 1;
            o << dot_idx << ";\n";

            dag.foreach_fanin(v, [&o, dot_idx] (auto f_id, int idx) {
                if (f_id != FANIN_PI) {
                    o << f_id << " -- " << dot_idx << ";\n";
                }
            });

        });

        o << "}\n";
    }
    
    enum partial_gen_type
    {
        GEN_TUPLES, /// No restrictions besides acyclicity
        GEN_CONNECTED, /// Generated graphs must be connected
        GEN_COLEX, /// Graph inputs must be co-lexicographically ordered
        GEN_NOREAPPLY, /// Graph inputs must not allow re-application of operators
    };

    class partial_dag_generator
    {
    private:
        int _nr_vertices;
        int _verbosity = 0;
        bool _initialized;
        int _level;
        uint64_t _nr_solutions;

        // Array indicating which steps have been covered. (And how many
        // times.) 
        int _covered_steps[18];

        // Array indicating which steps are "disabled", meaning that
        // selecting them will not result in a valid DAG.
        int _disabled_matrix[18][18][18];

        // If true, generates only connected DAGs.
        partial_gen_type _gen_type = GEN_NOREAPPLY;

        // The index at which backtracking should terminate.
        int _stop_level = -1;

        // Function to call when a solution is found.
        std::function<void(partial_dag_generator*)> _callback;

    public:
        partial_dag_generator() : _initialized(false) { }

        partial_dag_generator(int nr_vertices)
        {
            reset(nr_vertices);
        }

        // Two arrays that represent the "stack" of selected steps.
        int _js[18];
        int _ks[18];

        // The level from which the search is assumed to have started
        int _start_level = 1;

        int nr_vertices() const { return _nr_vertices; }

        void verbosity(int verbosity) { _verbosity = verbosity; }
        int verbosity() { return _verbosity; }

        partial_gen_type gen_type() const { return _gen_type; }
        void gen_type(partial_gen_type gen_type) { _gen_type = gen_type; }

        void set_callback(std::function<void(partial_dag_generator*)>& f)
        {
            _callback = f;
        }

        void set_callback(std::function<void(partial_dag_generator*)>&& f)
        {
            _callback = std::move(f);
        }

        void clear_callback()
        {
            _callback = 0;
        }

        void reset(int nr_vertices)
        {
            assert(nr_vertices > 0);

            if (_verbosity) {
                printf("setting nr. vertices=%d\n", nr_vertices);
            }

            _nr_vertices = nr_vertices;

            for (int i = 0; i < 18; i++) {
                _covered_steps[i] = 0;
            }

            for (int i = 0; i < 18; i++) {
                for (int j = 0; j < 18; j++) {
                    for (int k = 0; k < 18; k++) {
                        _disabled_matrix[i][j][k] = 0;
                    }
                }
            }

            // The first vertex can only point to PIs
            _js[0] = 0;
            _ks[0] = 0;

            _nr_solutions = 0;
            _level = 0;
            _stop_level = -1;

            _initialized = true;
        }

        auto count_tuples()
        {
            assert(_initialized);
            _level = _start_level;
            _nr_solutions = 0;

            search_tuples();

            return _nr_solutions;
        }

        void search_tuples()
        {
            if (_level == _nr_vertices) {
                ++_nr_solutions;
                if (_verbosity) {
                    printf("Found solution: ");
                    for (int i = 0; i < _nr_vertices; i++) {
                        const auto j = _js[i];
                        const auto k = _ks[i];
                        if (i > 0) {
                            printf(" - ");
                        }
                        printf("(%d, %d)", j, k);
                    }
                    printf("\n");
                }
                backtrack();
            } else {
                // It's always possible that this node is only connected to PIs
                _js[_level] = 0;
                _ks[_level] = 0;
                ++_level;
                search_tuples();
                for (int k = 1; k <= _level; k++) {
                    for (int j = 0; j < k; j++) {
                        _js[_level] = j;
                        _ks[_level] = k;
                        ++_level;
                        search_tuples();
                    }
                }
                backtrack();
            }
        }

        auto count_connected_dags()
        {
            assert(_initialized);
            _level = _start_level;
            _nr_solutions = 0;

            search_connected_dags();

            return _nr_solutions;
        }

        void search_connected_dags()
        {
            if (_level == _nr_vertices) {
                for (int i = 1; i <= _nr_vertices - 1; i++) {
                    if (_covered_steps[i] == 0) {
                        // There is some uncovered internal step, so the
                        // graph cannot be connected.
                        backtrack();
                        return;
                    }
                }
                ++_nr_solutions;
                if (_verbosity) {
                    printf("Found solution: ");
                    for (int i = 0; i < _nr_vertices; i++) {
                        const auto j = _js[i];
                        const auto k = _ks[i];
                        if (i > 0) {
                            printf(" - ");
                        }
                        printf("(%d, %d)", j, k);
                    }
                    printf("\n");
                }
                backtrack();
            } else {
                _js[_level] = 0;
                _ks[_level] = 0;
                ++_level;
                search_connected_dags();
                for (int k = 1; k <= _level; k++) {
                    for (int j = 0; j < k; j++) {
                        _js[_level] = j;
                        _ks[_level] = k;
                        ++_covered_steps[j];
                        ++_covered_steps[k];
                        ++_level;
                        search_connected_dags();
                    }
                }
                backtrack();
            }
        }

        auto count_colex_dags()
        {
            assert(_initialized);
            _level = 1;
            _nr_solutions = 0;

            search_colex_dags();

            return _nr_solutions;
        }

        void search_colex_dags()
        {
            if (_level == _nr_vertices) {
                for (int i = 1; i <= _nr_vertices - 1; i++) {
                    if (_covered_steps[i] == 0) {
                        // There is some uncovered internal step, so the
                        // graph cannot be connected.
                        backtrack();
                        return;
                    }
                }
                ++_nr_solutions;
                if (_verbosity) {
                    printf("Found solution: ");
                    for (int i = 0; i < _nr_vertices; i++) {
                        const auto j = _js[i];
                        const auto k = _ks[i];
                        if (i > 0) {
                            printf(" - ");
                        }
                        printf("(%d, %d)", j, k);
                    }
                    printf("\n");
                }
                backtrack();
            } else {
                // Check if this step can have pure PI fanins
                _js[_level] = 0;
                _ks[_level] = 0;
                ++_level;
                search_colex_dags();

                // We are only interested in DAGs that are in
                // co-lexicographical order. Look at the previous step
                // on the stack, the current step should be greater or
                // equal to it.
                const auto start_j = _js[_level - 1];
                auto start_k = _ks[_level - 1];

                if (start_j == start_k) { // Previous input has two PI inputs
                    ++start_k;
                }

                _ks[_level] = start_k;
                for (int j = start_j; j < start_k; j++) {
                    ++_covered_steps[j];
                    ++_covered_steps[start_k];
                    _js[_level] = j;
                    ++_level;
                    search_colex_dags();
                }
                for (int k = start_k + 1; k <= _level; k++) {
                    for (int j = 0; j < k; j++) {
                        ++_covered_steps[j];
                        ++_covered_steps[k];
                        _js[_level] = j;
                        _ks[_level] = k;
                        ++_level;
                        search_colex_dags();
                    }
                }

                backtrack();
            }
        }

        auto count_noreapply_dags()
        {
            assert(_initialized);
            _nr_solutions = 0;
            _level = 1;

            search_noreapply_dags();

            return _nr_solutions;
        }

        void search_noreapply_dags()
        {
            if (_level == _nr_vertices) {
                for (int i = 1; i <= _nr_vertices - 1; i++) {
                    if (_covered_steps[i] == 0) {
                        // There is some uncovered internal step, so the
                        // graph cannot be connected.
                        noreapply_backtrack();
                        return;
                    }
                }
                ++_nr_solutions;
                if (_verbosity) {
                    printf("Found solution: ");
                    for (int i = 0; i < _nr_vertices; i++) {
                        const auto j = _js[i];
                        const auto k = _ks[i];
                        if (i > 0) {
                            printf(" - ");
                        }
                        printf("(%d, %d)", j, k);
                    }
                    printf("\n");
                }
                if (_callback) {
                    _callback(this);
                }
                noreapply_backtrack();
            } else {
                // Check if this step can have pure PI fanins
                _js[_level] = 0;
                _ks[_level] = 0;
                ++_level;
                search_noreapply_dags();

                // We are only interested in DAGs that are in
                // co-lexicographical order. Look at the previous step
                // on the stack, the current step should be greater or
                // equal to it.
                const auto start_j = _js[_level - 1];
                auto start_k = _ks[_level - 1];

                if (start_j == start_k) { // Previous input has two PI inputs
                    ++start_k;
                }

                _ks[_level] = start_k;
                for (int j = start_j; j < start_k; j++) {
                    if (_disabled_matrix[_level][j][start_k]) {
                        continue;
                    }

                    // If we choose fanin (j, k), record that j and k
                    // are covered.
                    ++_covered_steps[j];
                    ++_covered_steps[start_k];

                    // We are adding step (i, j, k). This means that we
                    // don't have to consider steps (i',j,i) or (i',k,i)
                    // for i < i' <= n+r. This avoiding reapplying an
                    // operand.
                    for (int ip = _level + 1; ip < _nr_vertices; ip++) {
                        ++_disabled_matrix[ip][j][_level];
                        ++_disabled_matrix[ip][start_k][_level];
                    }

                    _js[_level] = j;
                    ++_level;
                    search_noreapply_dags();
                }
                for (int k = start_k + 1; k <= _level; k++) {
                    for (int j = 0; j < k; j++) {
                        if (_disabled_matrix[_level][j][k]) {
                            continue;
                        }
                        ++_covered_steps[j];
                        ++_covered_steps[k];

                        for (int ip = _level + 1; ip < _nr_vertices; ip++) {
                            ++_disabled_matrix[ip][j][_level];
                            ++_disabled_matrix[ip][k][_level];
                        }
                        _js[_level] = j;
                        _ks[_level] = k;
                        ++_level;
                        search_noreapply_dags();
                    }
                }

                noreapply_backtrack();
            }
        }

        void backtrack()
        {
            --_level;
            if (_level > _stop_level) {
                const auto j = _js[_level];
                const auto k = _ks[_level];
                --_covered_steps[j];
                --_covered_steps[k];
            }
        }

        void noreapply_backtrack()
        {
            --_level;
            const auto j = _js[_level];
            const auto k = _ks[_level];
            if (_level > _stop_level) {
                --_covered_steps[j];
                --_covered_steps[k];
                for (int ip = _level + 1; ip < _nr_vertices; ip++) {
                    --_disabled_matrix[ip][j][_level];
                    --_disabled_matrix[ip][k][_level];
                }
            }
        }

        auto count_dags()
        {
            switch (_gen_type) {
            case GEN_TUPLES:
                return count_tuples();
            case GEN_CONNECTED:
                return count_connected_dags();
            case GEN_COLEX:
                return count_colex_dags();
            default:
                return count_noreapply_dags();
            }
        }
    };


    /// Generate all partial DAGs up to the specified number
    /// of vertices.
    std::vector<partial_dag> pd_generate(int max_vertices)
    {
        partial_dag g;
        partial_dag_generator gen;
        std::vector<partial_dag> dags;

        gen.set_callback([&g, &dags]
        (partial_dag_generator* gen) {
            for (int i = 0; i < gen->nr_vertices(); i++) {
                g.set_vertex(i, gen->_js[i], gen->_ks[i]);
            }
            dags.push_back(g);
        });

        for (int i = 1; i <= max_vertices; i++) {
            g.reset(2, i);
            gen.reset(i);
            gen.count_dags();
        }

        return dags;
    }
}

