#pragma once

#include <vector>
#include <cassert>
#include <iostream>
#include <memory>

#include <kitty/kitty.hpp>
#include <kitty/print.hpp>
#include "dag.hpp"
#include "spec.hpp"
#include "misc.hpp"

using std::vector;
using std::unique_ptr;
using kitty::static_truth_table;
using kitty::dynamic_truth_table;
using kitty::create_nth_var;

/*******************************************************************************
    Definition of Boolean chain. A Boolean chain is a sequence of steps. Each
    step applies a Boolean operator to a fixed number of previous steps. The
    main objective of this package is to synthesize Boolean chains efficiently.
*******************************************************************************/
namespace percy
{

    template<int FI=2>
    class chain : public dag<FI>
    {
        public:
            using OpTT = static_truth_table<FI>;
            using fanin = typename dag<FI>::fanin;
            using dag<FI>::nr_inputs;
            using dag<FI>::nr_vertices;

        private:
            static const int OperandTTSize = (1 << FI);
            std::vector<OpTT> operators;
            std::vector<int> outputs;

        public:
            using dag = dag<FI>;

            chain() { }
            chain(const chain& c) = delete;

            chain(chain&& c)
            {
                dag::dag(c);
                outputs = std::move(c.outputs);
            }

            void reset(int nr_in, int nr_out, int nr_steps)
            {
                dag::reset(nr_in, nr_steps);
                operators.resize(nr_steps);
                outputs.resize(nr_out);
            }

            int get_nr_outputs() const { return outputs.size(); }
            const std::vector<int>& get_outputs() const { return outputs; }

            const OpTT& get_operator(int i) const
            {
              return operators.at(i);
            }

            std::vector<int>& get_outputs() { return outputs; }

            OpTT& get_operator(int i)
            {
              return operators.at(i);
            }

            bool
            is_output_inverted(int out_idx)
            {
                assert(out_idx < outputs.size());
                return outputs[out_idx] & 1;
            }

            void
            set_step(int i, const fanin* const in, const OpTT& op)
            {
                dag::set_vertex(i, in);
                operators[i] = op;
            }

            void
            set_step(int i, const std::array<fanin, FI>& in, const OpTT& op)
            {
                dag::set_vertex(i, in);
                operators[i] = op;
            }

            void
            add_step(const fanin* const in, const OpTT& op)
            {
                dag::add_vertex(in);
                operators.push_back(op);
            }

            void
            set_output(int out_idx, int lit)
            {
                outputs[out_idx] = lit;
            }

            void
            set_output(int out_idx, int step, bool invert)
            {
                outputs[out_idx] = (step << 1) | invert;
            }

            void 
            invert() 
            {
                for (int i = 0; i < outputs.size(); i++) {
                    outputs[i] = (outputs[i] ^ 1);
                }
            }
            
            /*******************************************************************
                De-normalizes a chain, meaning that all outputs will be
                converted to non-complemented edges. This may mean that some
                shared steps have to be duplicated or replaced by NOT gates.
                NOTE: some outputs may point to constants or PIs. These will
                not be changed.

                The use_nots flag may be used to insert NOT gates instead of
                duplicating inverted steps.
            *******************************************************************/
            void
            denormalize(const bool use_nots = false)
            {
                if (outputs.size() == 1) {
                    if (outputs[0] & 1) {
                        invert();
                    }
                    return;
                }

                std::vector<int> refcount(nr_vertices);
                std::vector<dynamic_truth_table> tmps(nr_vertices);
                std::vector<dynamic_truth_table> ins;
                std::vector<dynamic_truth_table> fs(outputs.size());

                for (int i = 1; i < nr_vertices; i++) {
                    const auto& v = dag::get_vertex(i);
                    foreach_fanin(v, [&refcount, nr_in=nr_inputs] (auto fid, int j) {
                        if (fid > nr_in) {
                            refcount[fid - nr_in - 1]++;
                        }
                    });
                }

                for (int i = 0; i < outputs.size(); i++) {
                    const auto step_idx = outputs[i] >> 1;
                    if (step_idx > nr_inputs) {
                        refcount[step_idx - nr_inputs - 1]++;
                    }
                }

                for (auto count : refcount) {
                    assert(count > 0);
                }

                for (auto i = 0; i < nr_inputs; ++i) {
                    auto in_tt = kitty::create<dynamic_truth_table>(nr_inputs);
                    ins.push_back(in_tt);
                }

                auto tt_step = kitty::create<dynamic_truth_table>(nr_inputs);
                auto tt_compute = kitty::create<dynamic_truth_table>(nr_inputs);
                
                for (int i = 0; i < nr_vertices; i++) {
                    const auto& step = dag::get_vertex(i);

                    dag::foreach_fanin(step,
                            [&ins, &tmps, nr_inputs=nr_inputs]
                            (auto fanin, int j) {
                        if (fanin < nr_inputs) {
                            create_nth_var(ins[j], fanin);
                        } else {
                            ins[j] = tmps[fanin - nr_inputs];
                        }
                    });

                    kitty::clear(tt_step);
                    for (int j = 1; j < OperandTTSize; j++) {
                        kitty::clear(tt_compute);
                        tt_compute = ~tt_compute;
                        if (get_bit(operators[i], j)) {
                            for (int k = 0; k < FI; k++) {
                                if ((j >> k) & 1) {
                                    tt_compute &= ins[k];
                                } else {
                                    tt_compute &= ~ins[k];
                                }
                            }
                            tt_step |= tt_compute;
                        }
                    }
                    tmps[i] = tt_step;

                    for (int h = 0; h < outputs.size(); h++) {
                        const auto out = outputs[h];
                        const auto var = out >> 1;
                        const auto inv = out & 1;
                        if (var - nr_inputs - 1 == i) {
                            fs[h] = inv ? ~tt_step : tt_step;
                        }
                    }
                }
                
                for (int i = 0; i < outputs.size(); i++) {
                    auto step_idx = outputs[i] >> 1;
                    const auto invert = outputs[i] & 1;

                    if (!invert || step_idx <= nr_inputs) {
                        continue;
                    }

                    step_idx -= (nr_inputs + 1);
                    assert(refcount[step_idx] >= 1);
                    if (refcount[step_idx] == 1) {
                        operators[step_idx] = ~operators[step_idx];
                    } else {
                        // This output points to a shared step that needs to
                        // be inverted. If no inverted version of this step
                        // exists somewhere in the chain, we need to add a new
                        // step.
                        bool inv_step_found = false;
                        for (int j = 0; j < nr_vertices; j++) {
                            if (tmps[j] == fs[i]) {
                                set_output(i, j + nr_inputs + 1, false);
                                inv_step_found = true;
                            }
                        }
                        if (inv_step_found) {
                            continue;
                        }
                        fanin fanins[FI];
                        const auto& v = dag::get_vertex(step_idx);
                        foreach_fanin(v, [&fanins] (auto fid, int j) {
                            fanins[j] = fid;
                        });

                        add_step(fanins, ~operators[step_idx]);
                        set_output(i, nr_inputs + nr_vertices, false);
                        tmps.push_back(fs[i]);

                        refcount[step_idx]--;
                    }
                }
            }

            /*******************************************************************
                Derive truth tables from the chain, one for each output.
            *******************************************************************/
            template<typename TT>
            std::vector<TT>
            simulate(const synth_spec<TT>& spec) /*const*/
            {
                std::vector<TT> fs(outputs.size());
                std::vector<TT> tmps(nr_vertices);
                std::vector<TT> ins;

                for (auto i = 0; i < nr_inputs; ++i) {
                    ins.push_back(kitty::create<TT>(nr_inputs));
                }

                auto tt_step = kitty::create<TT>(nr_inputs);
                auto tt_compute = kitty::create<TT>(nr_inputs);

                // Some outputs may be simple constants or projections.
                for (int h = 0; h < outputs.size(); h++) {
                    const auto out = outputs[h];
                    const auto var = out >> 1;
                    const auto inv = out & 1;
                    if (var == 0) {
                        clear(tt_step);
                        fs[h] = inv ? ~tt_step : tt_step;
                    } else if (var <= nr_inputs) {
                        create_nth_var(tt_step, var-1, inv);
                        fs[h] = tt_step;
                    }
                }

                for (int i = 0; i < nr_vertices; i++) {
                    const auto& step = dag::get_vertex(i);

                    dag::foreach_fanin(step,
                            [&ins, &tmps, nr_inputs=nr_inputs]
                            (auto fanin, int j) {
                        if (fanin < nr_inputs) {
                            create_nth_var(ins[j], fanin);
                        } else {
                            ins[j] = tmps[fanin - nr_inputs];
                        }
                    });

                    kitty::clear(tt_step);
                    for (int j = 0; j < OperandTTSize; j++) {
                        kitty::clear(tt_compute);
                        tt_compute = ~tt_compute;
                        if (get_bit(operators[i], j)) {
                            for (int k = 0; k < FI; k++) {
                                if ((j >> k) & 1) {
                                    tt_compute &= ins[k];
                                } else {
                                    tt_compute &= ~ins[k];
                                }
                            }
                            tt_step |= tt_compute;
                        }
                    }
                    tmps[i] = tt_step;

                    for (int h = 0; h < outputs.size(); h++) {
                        const auto out = outputs[h];
                        const auto var = out >> 1;
                        const auto inv = out & 1;
                        if (var - nr_inputs - 1 == i) {
                            fs[h] = inv ? ~tt_step : tt_step;
                        }
                    }
                }

                return fs;
            }


            /*******************************************************************
                Checks if a chain satisfies the given specification. This
                checks not just if the chain computes the correct function, but
                also other requirements such as co-lexicogrpahic order (if
                specified).
            *******************************************************************/
            template<typename TT>
            bool
            satisfies_spec(const synth_spec<TT>& spec)
            {
                if (spec.nr_triv == spec.get_nr_out()) {
                    return true;
                }
                auto tts = simulate(spec);
                static_truth_table<FI> op_tt;

                if (spec.nr_steps != nr_vertices) {
                    assert(false);
                    return false;
                }

                auto nr_nontriv = 0;
                for (int i = 0; i < spec.nr_nontriv; i++) {
                    if ((spec.triv_flag >> i) & 1) {
                        continue;
                    }
                    if (tts[nr_nontriv++] != *spec.functions[i]) {
                        assert(false);
                        return false;
                    }
                }

                if (spec.add_nontriv_clauses) {
                    // Ensure that there are no trivial operators.
                    for (auto& op : operators) {
                        clear(op_tt);
                        if (op == op_tt) {
                            assert(false);
                            return false;
                        }
                        for (int i = 0; i < FI; i++) {
                            create_nth_var(op_tt, i);
                            if (op == op_tt) {
                                assert(false);
                                return false;
                            }
                        }
                    }
                }

                if (spec.add_alonce_clauses) {
                    // Ensure that each step is used at least once.
                    std::vector<int> nr_uses(nr_vertices);

                    for (int i = 1; i < nr_vertices; i++) {
                        const auto& vertex = dag::get_vertex(i);
                        foreach_fanin(vertex, [&nr_uses, nr_inputs=nr_inputs]
                            (auto fid, int j) {
                                if (fid >= nr_inputs) {
                                    nr_uses[fid-nr_inputs]++;
                                }
                            }
                        );
                    }
                    for (auto output : outputs) {
                        const auto step_idx = output >> 1;
                        if (step_idx > nr_inputs) {
                            nr_uses[step_idx-nr_inputs-1]++;
                        }
                    }

                    for (auto nr : nr_uses) {
                        if (nr == 0) {
                            assert(false);
                            return false;
                        }
                    }
                }

                if (spec.add_noreapply_clauses) {
                    // Ensure there is no re-application of operands.
                    for (int i = 0; i < nr_vertices - 1; i++) {
                        fanin fanins1[FI];
                        const auto& v = dag::get_vertex(i);
                        foreach_fanin(v, [&fanins1] (auto fid, int j) {
                            fanins1[j] = fid;
                        });

                        for (int ip = i + 1; ip < nr_vertices; ip++) {
                            fanin fanins2[FI];
                            const auto& v2 = dag::get_vertex(i);
                            foreach_fanin(v2, 
                                    [&fanins2] (auto fid, int j) {
                                fanins2[j] = fid;
                            });

                            auto is_subsumed = true;
                            auto has_fanin_i = false;
                            for (auto j : fanins2) {
                                if (j == i + nr_inputs) {
                                    has_fanin_i = true;
                                    continue;
                                }
                                auto is_included = false;
                                for (auto jp : fanins1) {
                                    if (j == jp) {
                                        is_included = true;
                                    }
                                }
                                if (!is_included) {
                                    is_subsumed = false;
                                }
                            }
                            if (is_subsumed && has_fanin_i) {
                                assert(false);
                                return false;
                            }
                        }
                    }
                }

                if (spec.add_colex_clauses) {
                    // Ensure that steps are in co-lexicographical order.
                    for (int i = 0; i < spec.nr_steps - 1; i++) {
                        const auto& v1 = dag::get_vertex(i);
                        const auto& v2 = dag::get_vertex(i + 1);
                        
                        fanin fanins1[FI];
                        foreach_fanin(v1, [&fanins1] (auto fid, int j) {
                            fanins1[j] = fid;
                        });

                        fanin fanins2[FI];
                        foreach_fanin(v2, [&fanins2] (auto fid, int j) {
                            fanins2[j] = fid;
                        });

                        if (colex_compare<fanin, FI>(fanins1, fanins2) == 1) {
                            assert(false);
                            return false;
                        }
                    }
                }

                if (spec.add_lex_clauses) {
                    // Ensure that steps are in lexicographical order.
                    for (int i = 0; i < spec.nr_steps - 1; i++) {
                        const auto& v1 = dag::get_vertex(i);
                        const auto& v2 = dag::get_vertex(i + 1);
                        
                        fanin fanins1[FI];
                        foreach_fanin(v1, [&fanins1] (auto fid, int j) {
                            fanins1[j] = fid;
                        });

                        fanin fanins2[FI];
                        foreach_fanin(v2, [&fanins2] (auto fid, int j) {
                            fanins2[j] = fid;
                        });

                        if (lex_compare<fanin, FI>(fanins1, fanins2) == 1) {
                            assert(false);
                            return false;
                        }
                    }
                }

                if (spec.add_lex_func_clauses) {
                    // Ensure that step operators are in lexicographical order.
                    for (int i = 0; i < spec.nr_steps - 1; i++) {
                        const auto& v1 = dag::get_vertex(i);
                        const auto& v2 = dag::get_vertex(i + 1);

                        fanin fanins1[FI];
                        foreach_fanin(v1, [&fanins1] (auto fid, int j) {
                            fanins1[j] = fid;
                        });

                        fanin fanins2[FI];
                        foreach_fanin(v2, [&fanins2] (auto fid, int j) {
                            fanins2[j] = fid;
                        });

                        if (colex_compare<fanin, FI>(fanins1, fanins2) == 0) {
                            // The operator of step i must be lexicographically
                            // less than that of i + 1.
                            const auto& op1 = operators[i];
                            const auto& op2 = operators[i + 1];
                            if (op2 < op1) {
                                assert(false);
                                return false;
                            }
                        }
                    }
                }

                if (spec.add_symvar_clauses) {
                    // Ensure that symmetric variables are ordered.
                    for (int q = 1; q < spec.get_nr_in(); q++) {
                        for (int p = 0; p < q; p++) {
                            auto symm = true;
                            for (int i = 0; i < spec.get_nr_out(); i++) {
                                auto outfunc = spec.functions[i];
                                if (!(swap(*outfunc, p, q) == *outfunc)) {
                                    symm = false;
                                    break;
                                }
                            }
                            if (!symm) {
                                continue;
                            }
                            for (int i = 1; i < spec.nr_steps; i++) {
                                const auto& v1 = dag::get_vertex(i);
                                auto has_fanin_p = false;
                                auto has_fanin_q = false;

                                foreach_fanin(v1, 
                                        [p, q, &has_fanin_p, &has_fanin_q] 
                                        (auto fid, int j) {
                                            if (fid == p) {
                                                has_fanin_p = true;
                                            } else if (fid == q) {
                                                has_fanin_q = true;
                                            }
                                        }
                                );
                                if (!has_fanin_q || has_fanin_p) {
                                    continue;
                                }
                                auto p_in_prev_step = false;
                                for (int ip = 0; ip < i; ip++) {
                                    const auto& v2 = dag::get_vertex(ip);
                                    has_fanin_p = false;

                                    foreach_fanin(v2, [p, q, &has_fanin_p] 
                                        (auto fid, int j) {
                                            if (fid == p) {
                                                has_fanin_p = true;
                                            }
                                        }
                                    );
                                    if (has_fanin_p) {
                                        p_in_prev_step = true;
                                    }   
                                }
                                if (!p_in_prev_step) {
                                    assert(false);
                                    return false;
                                }
                            }
                        }
                    }
                }

                return true;
            }

            void
            copy(const chain<FI>& c)
            {
                copy_dag(c);
                outputs = c.outputs;
            }

            /*******************************************************************
                Creates a DAG from the Boolean chain in .dot format, so that
                it may be rendered using various DAG packages (e.g. graphviz).
            *******************************************************************/
            void
            to_dot(std::ostream& s) /* NOTE: deprecated impl. */
            {
                s << "graph {\n";
                s << "rankdir = BT\n";
                s << "x0 [shape=none,label=<\u22A5>];\n";
                for (int i = 0; i < dag::nr_inputs; i++) {
                    const auto idx = i + 1;
                    s << "x" << idx << " [shape=none,label=<x<sub>" << idx
                        << "</sub>>];\n";
                }

                s << "node [shape=circle];\n";
                for (size_t i = 0; i < dag::nr_vertices; i++) {
                    const auto& step = dag::vertices[i];
                    const auto idx = dag::nr_inputs + i + 1;
                    s << "x" << idx << " [label=<";
                    kitty::print_binary(operators[i], s);
                    s << ">];\n";
                    for (int j = 0; j < FI; j++) {
                        s << "x" << step.inputs[j]+1 << " -- x" << idx << ";\n";
                    }
                }

                for (size_t h = 0u; h < outputs.size(); h++) {
                    const auto out = outputs[h];
                    const auto inv = out & 1;
                    const auto var = out >> 1;
                    s << "f" << h << " [shape=none,label=<f<sub>" << h+1
                        << "</sub>>];\n";
                    s << "x" << var << " -- f" << h << " [style=" <<
                        (inv ? "dashed" : "solid") << "];\n";
                }

                // Group inputs on same level.
                s << "{rank = same; x0; ";
                for (int i = 0; i < dag::nr_inputs; i++) {
                    s << "x" << i+1 << "; ";
                }
                s << "}\n";

                // Group outputs on same level.
                s << "{rank = same; ";
                for (size_t h = 0u; h < outputs.size(); h++) {
                    s << "f" << h << "; ";
                }
                s << "}\n";

                // Add invisible edges between PIs and POs to enforce order.
                s << "edge[style=invisible];\n";
                for (int i = dag::nr_inputs; i > 0; i--) {
                    s << "x" << i-1 << " -- x" << i << ";\n";
                }
                for (size_t h = outputs.size(); h > 1; h--) {
                    s << "f" << h-2 << " -- f" << h-1 << ";\n";
                }

                s << "}\n";

            }

            void
            print_dot()
            {
                to_dot(std::cout);
            }

            /*******************************************************************
                Functions to convert the chain to a parseable expression.
                Currently only supported for single-output normal chains with
                2-input operators.
            *******************************************************************/
            void
            step_to_expression(std::ostream& s, int step_idx)
            {
                if (step_idx < dag::nr_inputs) {
                    s << char(('a' + step_idx));
                    return;
                }
                const auto& step = dag::get_vertex(step_idx - nr_inputs);
                auto word = 0;
                for (int i = 0; i < 4; i++) {
                    if (kitty::get_bit(operators[step_idx - nr_inputs], i)) {
                        word |= (1 << i);
                    }
                }
                assert(word <= 15);
                switch (word) {
                    case 2:
                        s << "(";
                        step_to_expression(s, step.first);
                        s << "!";
                        step_to_expression(s, step.second);
                        s << ")";
                        break;
                    case 4:
                        s << "(";
                        s << "!";
                        step_to_expression(s, step.first);
                        step_to_expression(s, step.second);
                        s << ")";
                        break;
                    case 6:
                        s << "[";
                        step_to_expression(s, step.first);
                        step_to_expression(s, step.second);
                        s << "]";
                        break;
                    case 8:
                        s << "(";
                        step_to_expression(s, step.first);
                        step_to_expression(s, step.second);
                        s << ")";
                        break;
                    case 14:
                        s << "{";
                        step_to_expression(s, step.first);
                        step_to_expression(s, step.second);
                        s << "}";
                        break;
                    default:
                        // Invalid operator detected.
                        printf("Invalid operator %d\n", word);
                        assert(0);
                        break;
                }
            }

            void
            to_expression(std::ostream& s)
            {
                assert(outputs.size() == 1 && FI == 2);
                const auto outlit = outputs[0];
                if (outlit & 1) {
                    s << "!";
                }
                const auto outvar = outlit >> 1;
                if (outvar == 0) { // Special case of constant 0
                    s << "0";
                } else {
                    step_to_expression(s, outvar-1);
                }
            }

            void
            print_expression()
            {
                to_expression(std::cout);
            }

            void
            extract_dag(dag& g) const
            {
                g.copy_dag(*this);
            }

    };

}

