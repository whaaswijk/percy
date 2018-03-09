#pragma once

#include <vector>
#include <cassert>
#include <iostream>
#include <memory>

#include <kitty/kitty.hpp>
#include <kitty/print.hpp>
#include "dag.hpp"

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

    /***************************************************************************
        A step has a fixed number of inputs, determined by StepSize.
    ***************************************************************************/
    template<int StepSize=2>
    struct step
    {
        static_truth_table<StepSize> op;
        int inputs[StepSize];
    };


    template<typename TT, int StepSize=2>
    class chain
    {
        private:
            int _nr_in;
            const int _op_tt_size = (1 << StepSize);
            std::vector<step<StepSize>> _steps;
            std::vector<int> _outs;

        public:
            chain() { reset(0, 0, 0); }
            chain(const chain& c) = delete;

            chain(chain&& c)
            {
                _nr_in = c._nr_in;
                _outs = std::move(c._outs);
                _steps = std::move(c._steps);
            }

            void reset(int nr_in, int nr_out, int nr_steps)
            {
                _nr_in = nr_in;
                _outs.resize(nr_out);
                _steps.resize(nr_steps);
            }

            int nr_in() const { return _nr_in; }
            int nr_out() const { return _outs.size(); }
            int nr_steps() const { return _steps.size(); }
            const std::vector<step<StepSize>>& steps() const { return _steps; }
            const std::vector<int>& outs() const { return _outs; }

            void 
            set_step(unsigned i, const static_truth_table<StepSize>& op, 
                    const int* inputs)
            {
                _steps[i].op = op;
                for (int j = 0; j < StepSize; j++) {
                    _steps[i].inputs[j] = inputs[j];
                }
            }
            
            void set_out(unsigned h, int lit)
            {
                _outs[h] = lit;
            }

            void invert() {
                for (int i = 0; i < nr_out(); i++) {
                    _outs[i] = (_outs[i] ^ 1);
                }
            }

            /*******************************************************************
                Derive truth tables from the chain, one for each output.
            *******************************************************************/
            vector<unique_ptr<TT>> simulate() const
            {
                vector<unique_ptr<TT>> fs(nr_out());
                vector<unique_ptr<TT>> tmps(nr_steps());
                TT ins[StepSize]; 
                TT tt_step; 
                TT tt_compute; 

                // Some outputs may be simple constants or projections.
                for (int h = 0; h < nr_out(); h++) {
                    const auto out = _outs[h];
                    const auto var = out >> 1;
                    const auto inv = out & 1;
                    if (var == 0) {
                        clear(tt_step);
                        fs[h].reset(new TT(inv ? unary_not(tt_step) : tt_step));
                    } else if (var <= nr_in()) {
                        create_nth_var(tt_step, var-1, inv);
                        fs[h].reset(new TT(tt_step));
                    }
                }

                for (int i = 0; i < nr_steps(); i++) {
                    const auto& step = _steps[i];

                    for (int j = 0; j < StepSize; j++) {
                        if (step.inputs[j] < nr_in()) {
                            create_nth_var(ins[j], step.inputs[j]);
                        } else {
                            ins[j] = *tmps[step.inputs[j]-nr_in()];
                        }
                    }

                    kitty::clear(tt_step);
                    for (int j = 1; j < _op_tt_size; j++) {
                        kitty::clear(tt_compute);
                        tt_compute = ~tt_compute;
                        if (get_bit(step.op, j)) {
                            for (int k = 0; k < StepSize; k++) {
                                if ((j >> k) & 1) {
                                    tt_compute &= ins[k];
                                } else {
                                    tt_compute &= unary_not(ins[k]);
                                }
                            }
                            tt_step |= tt_compute;
                        }
                    }
                    tmps[i].reset(new TT(tt_step));

                    for (int h = 0; h < nr_out(); h++) {
                        const auto out = _outs[h];
                        const auto var = out >> 1;
                        const auto inv = out & 1;
                        if (var - nr_in() - 1 == i) {
                            fs[h].reset(new TT(inv ?  ~tt_step : tt_step));
                        }
                    }
                }

                return fs;
            }

            /*
            template<>
            vector<unique_ptr<dynamic_truth_table>> simulate()
            {
                vector<unique_ptr<dynamic_truth_table>> fs(nr_out());
                vector<unique_ptr<dynamic_truth_table>> tmps(nr_steps());
                unique_ptr<dynamic_truth_table> ins[StepSize]; 
                for (int i = 0; i < StepSize; i++) {
                    ins[i].reset(new dynamic_truth_table(_nr_in));
                }
                dynamic_truth_table tt_step(_nr_in); 
                dynamic_truth_table tt_compute(_nr_in); 


                // Some outputs may be simple constants or projections.
                for (int h = 0; h < nr_out(); h++) {
                    const auto out = _outs[h];
                    const auto var = out >> 1;
                    const auto inv = out & 1;
                    if (var == 0) {
                        fs[h].reset(new dynamic_truth_table(inv ?
                                    unary_not(tt_step) : tt_step));
                    } else if (var <= nr_in()) {
                        create_nth_var(tt_step, var-1, inv);
                        fs[h].reset(new dynamic_truth_table(tt_step));
                    }
                }

                for (int i = 0; i < nr_steps(); i++) {
                    const auto& step = _steps[i];

                    for (int j = 0; j < StepSize; j++) {
                        if (step.inputs[j] < nr_in()) {
                            create_nth_var(ins[j], step.inputs[j]);
                        } else {
                            *ins[j] = *tmps[step.inputs[j]-nr_in()];
                        }
                    }

                    kitty::clear(tt_step);
                    for (int j = 1; j < _op_tt_size; j++) {
                        kitty::clear(tt_compute);
                        tt_compute = ~tt_compute;
                        if (get_bit(step.op, j)) {
                            for (int k = 0; k < StepSize; k++) {
                                if ((j >> k) & 1) {
                                    tt_compute &= *ins[k];
                                } else {
                                    tt_compute &= *unary_not(ins[k]);
                                }
                            }
                            tt_step |= tt_compute;
                        }
                    }
                    tmps[i].reset(new dynamic_truth_table(tt_step));

                    for (int h = 0; h < nr_out(); h++) {
                        const auto out = _outs[h];
                        const auto var = out >> 1;
                        const auto inv = out & 1;
                        if (var - nr_in() - 1 == i) {
                            fs[h].reset(new dynamic_truth_table(inv ? 
                                        ~tt_step : tt_step));
                        }
                    }
                }

                return fs;
            }
            */

            void copy(const chain<TT,StepSize>& c) {
                _nr_in = c._nr_in;
                _outs = c.outs();
                _steps.resize(c.nr_steps());
                for (int i = 0; i < c.nr_steps(); i++) {
                    const auto& step = c._steps[i];
                    set_step(i, step.op, step.inputs);
                }
            }

            /*******************************************************************
                Creates a DAG from the Boolean chain in .dot format, so that
                it may be rendered using various DAG packages (e.g. graphviz).
            *******************************************************************/
            void to_dot(std::ostream& s)
            {
                s << "graph {\n";
                s << "rankdir = BT\n";
                s << "x0 [shape=none,label=<\u22A5>];\n";
                for (int i = 0; i < _nr_in; i++) {
                    const auto idx = i + 1;
                    s << "x" << idx << " [shape=none,label=<x<sub>" << idx 
                        << "</sub>>];\n";
                }

                s << "node [shape=circle];\n";
                for (size_t i = 0; i < _steps.size(); i++) {
                    const auto& step = _steps[i];
                    const auto idx = _nr_in + i + 1;
                    s << "x" << idx << " [label=<";
                    kitty::print_binary(step.op, s);
                    s << ">];\n";
                    for (int j = 0; j < StepSize; j++) {
                        s << "x" << step.inputs[j]+1 << " -- x" << idx << ";\n";
                    }
                }

                for (size_t h = 0u; h < _outs.size(); h++) {
                    const auto out = _outs[h];
                    const auto inv = out & 1;
                    const auto var = out >> 1;
                    s << "f" << h << " [shape=none,label=<f<sub>" << h+1 
                        << "</sub>>];\n";
                    s << "x" << var << " -- f" << h << " [style=" <<
                        (inv ? "dashed" : "solid") << "];\n";
                }

                // Group inputs on same level.
                s << "{rank = same; x0; ";
                for (int i = 0; i < _nr_in; i++) {
                    s << "x" << i+1 << "; ";
                }
                s << "}\n";

                // Group outputs on same level.
                s << "{rank = same; ";
                for (size_t h = 0u; h < _outs.size(); h++) {
                    s << "f" << h << "; ";
                }
                s << "}\n";

                // Add invisible edges between PIs and POs to enforce order.
                s << "edge[style=invisible];\n";
                for (int i = _nr_in; i > 0; i--) {
                    s << "x" << i-1 << " -- x" << i << ";\n";
                }
                for (size_t h = _outs.size(); h > 1; h--) {
                    s << "f" << h-2 << " -- f" << h-1 << ";\n";
                }

                s << "}\n";

            }

            void print_dot()
            {
                to_dot(std::cout);
            }

            /*******************************************************************
                Functions to convert the chain to a parseable expression.
                Currently only supported for single-output normal chains with
                2-input operators.
            *******************************************************************/
            void step_to_expression(std::ostream& s, int step_idx) 
            {
                if (step_idx < _nr_in) {
                    s << char(('a' + step_idx));
                    return;
                }
                const auto& step = _steps[step_idx - _nr_in];
                auto word = 0;
                for (int i = 0; i < 4; i++) {
                    if (get_bit(step.op, i)) {
                        word |= (1 << i);
                    }
                }
                assert(word <= 15);
                switch (word) {
                    case 2:
                        s << "(";
                        step_to_expression(s, step.inputs[0]);
                        s << "!";
                        step_to_expression(s, step.inputs[1]);
                        s << ")";
                        break;
                    case 4:
                        s << "(";
                        s << "!";
                        step_to_expression(s, step.inputs[0]);
                        step_to_expression(s, step.inputs[1]);
                        s << ")";
                        break;
                    case 6:
                        s << "[";
                        step_to_expression(s, step.inputs[0]);
                        step_to_expression(s, step.inputs[1]);
                        s << "]";
                        break;
                    case 8:
                        s << "(";
                        step_to_expression(s, step.inputs[0]);
                        step_to_expression(s, step.inputs[1]);
                        s << ")";
                        break;
                    case 14:
                        s << "{";
                        step_to_expression(s, step.inputs[0]);
                        step_to_expression(s, step.inputs[1]);
                        s << "}";
                        break;
                    default:
                        // Invalid operator detected.
                        printf("Invalid operator %d\n", word);
                        assert(0);
                        break;
                }
            }

            void to_expression(std::ostream& s)
            {
                assert(_outs.size() == 1 && StepSize == 2);
                const auto outlit = _outs[0];
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

            void print_expression()
            {
                to_expression(std::cout);
            }

            void extract_dag(dag& g) const
            {
                const auto nr_steps = _steps.size();
                g.reset(_nr_in, nr_steps);
                for (int i = 0; i < nr_steps; i++) {
                    const auto& step = _steps[i];
                    g.set_vertex(i, step.inputs[0], step.inputs[1]);
                }
            }

    };

}

