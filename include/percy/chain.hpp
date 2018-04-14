#pragma once

#include <vector>
#include <cassert>
#include <iostream>
#include <memory>

#include <kitty/kitty.hpp>
#include <kitty/print.hpp>
#include "dag.hpp"
#include "spec.hpp"

using std::vector;
using std::unique_ptr;
using kitty::static_truth_table;
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
            set_output(int out_idx, int lit)
            {
                outputs[out_idx] = lit;
            }

            void invert() {
                for (int i = 0; i < outputs.size(); i++) {
                    outputs[i] = (outputs[i] ^ 1);
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

                return fs;
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

