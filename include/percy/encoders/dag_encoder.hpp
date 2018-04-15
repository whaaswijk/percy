#pragma once

#include "encoder_base.hpp"
#include "../io.hpp"

namespace percy
{
    template<typename Dag, typename Solver=sat_solver*>
    class dag_encoder
    {
        using fanin = typename Dag::fanin;

        private:
            // We only keep a reference to the solver. Since we don't own it,
            // we should never use encoders outside of the synthesizer objects
            // that own them and the solvers.
            Solver* solver;

            int nr_op_vars;
            int nr_sim_vars;
            int nr_op_vars_per_step;

            abc::Vec_Int_t* vLits; // Dynamic vector of literals

        public:
            dag_encoder()
            {
                vLits = abc::Vec_IntAlloc(128);
            }

            ~dag_encoder()
            {
                abc::Vec_IntFree(vLits);
            }

            void 
            set_solver(Solver* s)
            {
                solver = s;
            }

            int
            get_op_var(const Dag& dag, int step_idx, int var_idx)
            {
                assert(step_idx < dag.get_nr_vertices());
                assert(var_idx > 0);
                assert(var_idx <= nr_op_vars_per_step);

                return step_idx * nr_op_vars_per_step + var_idx - 1;
            }

            template<typename TT>
            int
            get_sim_var(
                    const synth_spec<TT>& spec, const Dag& dag,
                    int step_idx, 
                    int t)
            {
                assert(step_idx < dag.get_nr_vertices());

                return nr_op_vars + spec.get_tt_size() * step_idx + t;
            }

            template<typename TT>
            void
            create_variables(const synth_spec<TT>& spec, const Dag& dag)
            {
                nr_op_vars_per_step = ((1u << Dag::NrFanin) - 1);
                nr_op_vars = dag.get_nr_vertices() * nr_op_vars_per_step;
                nr_sim_vars = dag.get_nr_vertices() * spec.get_tt_size();
                if (spec.verbosity > 1) {
                    printf("nr_op_vars_per_step=%d\n", nr_op_vars_per_step);
                    printf("nr_op_vars=%d\n", nr_op_vars);
                    printf("nr_sim_vars=%d\n", nr_sim_vars);
                }

                solver_set_nr_vars(*solver, nr_op_vars + nr_sim_vars);
            }

            template<typename TT>
            bool
            add_simulation_clause(
                    const synth_spec<TT>& spec,
                    const Dag& dag,
                    const int t, 
                    const int i, 
                    const int output, 
                    const int opvar_idx,
                    const fanin* const fanins,
                    const std::bitset<Dag::NrFanin>& fanin_asgn)
            {
                int ctr = 0;

                for (int j = 0; j < Dag::NrFanin; j++) {
                    auto child = fanins[j];
                    auto assign = fanin_asgn[j];
                    if (child < spec.get_nr_in()) {
                        if (( ( (t + 1) & (1 << child) ) ? 1 : 0 ) != assign) {
                            return true;
                        }
                    } else {
                        abc::Vec_IntSetEntry(vLits, ctr++, abc::Abc_Var2Lit(
                                    get_sim_var(spec, dag, child -
                                        spec.get_nr_in(), t), assign));
                    }
                }

                abc::Vec_IntSetEntry(vLits, ctr++,
                        abc::Abc_Var2Lit(get_sim_var(spec, dag, i, t), output));

                if (opvar_idx > 0) {
                    abc::Vec_IntSetEntry(vLits, ctr++, abc::Abc_Var2Lit(
                                get_op_var(dag, i, opvar_idx), 1 - output));
                }

                auto status =  solver_add_clause(*solver,
                        abc::Vec_IntArray(vLits), 
                        abc::Vec_IntArray(vLits) + ctr); 

                if (spec.verbosity > 2) {
                    printf("creating sim. clause: (");
                    printf(" %sx_%d_%d ", output ? "!" : "", 
                            spec.get_nr_in() + i + 1, t + 2);

                    for (int j = 0; j < Dag::NrFanin; j++) {
                        auto child = fanins[j];
                        auto assign = fanin_asgn[j];
                        if (child < spec.get_nr_in()) {
                            continue;
                        }
                        printf(" \\/ %sx_%d_%d ",
                                    assign ? "!" : "", child + 1, t + 2);
                    }
                    if (opvar_idx > 0) {
                        printf(" \\/ %sf_%d_%d ", 
                                (1-output) ? "!" : "", 
                                spec.get_nr_in() + i + 1, opvar_idx + 1);
                    }
                    printf(") (status=%d)\n", status);
                }

                return status;
            }

            template<typename TT>
            bool
            create_tt_clauses(
                    const synth_spec<TT>& spec, 
                    const Dag& dag, 
                    int t)
            {
                fanin fanins[Dag::NrFanin];
                std::bitset<Dag::NrFanin> fanin_asgn;

                for (int i = 0; i < dag.get_nr_vertices(); i++) {
                    auto v = dag.get_vertex(i);
                    dag.foreach_fanin(v, [&fanins] (auto f_id, int j) {
                        fanins[j] = f_id;
                    });

                    // First add clauses for all cases where the operator i
                    // computes zero.
                    int opvar_idx = 0;
                    clear_assignment<Dag::NrFanin>(fanin_asgn);
                    while (true) {
                        next_assignment<Dag::NrFanin>(fanin_asgn);
                        if (is_zero<Dag::NrFanin>(fanin_asgn)) {
                            break;
                        }
                        opvar_idx++;
                        if (!add_simulation_clause(spec, dag, t, i, 0,
                                    opvar_idx, fanins, fanin_asgn)) {
                            return false;
                        }
                    }

                    // Next, all cases where operator i computes one.
                    opvar_idx = 0;
                    if (!add_simulation_clause(spec, dag, t, i, 1, opvar_idx,
                                fanins, fanin_asgn)) {
                        return false;
                    }
                    while (true) {
                        next_assignment<Dag::NrFanin>(fanin_asgn);
                        if (is_zero<Dag::NrFanin>(fanin_asgn)) {
                            break;
                        }
                        opvar_idx++;
                        if (!add_simulation_clause(spec, dag, t, i, 1, opvar_idx,
                                fanins, fanin_asgn)) {
                            return false;
                        }
                    }

                    // If an output has selected this particular operand, we
                    // need to ensure that this operand's truth table satisfies
                    // the specified output function.
                    if (i == dag.get_nr_vertices()-1) {
                        int pLits[1];
                        auto outbit = kitty::get_bit(*spec.functions[0], t+1);
                        if (spec.out_inv & 1) {
                            outbit = 1 - outbit;
                        }
                        pLits[0] = abc::Abc_Var2Lit(get_sim_var(spec, dag, i,
                                    t), 1 - outbit);
                        if (!solver_add_clause(*solver,pLits,pLits+1)) {
                            return false;
                        }

                        if (spec.verbosity > 1) {
                            printf("bit %d=%d", t+2, outbit);
                            printf("\tvar=%d\n", get_sim_var(spec, dag, i, t));
                        }
                    }
                }

                return true;
            }

            template<typename TT>
            bool
            create_main_clauses(const synth_spec<TT>& spec, const Dag& dag)
            {
                for (int t = 0; t < spec.get_tt_size(); t++) {
                    if (!create_tt_clauses(spec, dag, t)) {
                        return false;
                    }
                }
                return true;
            }

            template<typename TT>
            bool 
            encode(const synth_spec<TT>& spec, const Dag& dag)
            {
                bool success = true;
                create_variables(spec, dag);
                success &= create_main_clauses(spec, dag);
                // success &= create_nontriv_clauses();
                return success;
            }

            template<typename TT>
            bool 
            cegar_encode(const synth_spec<TT>& spec, const Dag& dag)
            {
                create_variables(spec, dag);
                for (int i = 0; i < spec.nr_rand_tt_assigns; i++) {
                    const auto t = rand() % spec.get_tt_size();
                    if (!create_tt_clauses(spec, dag, t)) {
                        return false;
                    }
                }
                return true;
            }

            template<typename TT>
            void 
            extract_chain(
                    const synth_spec<TT>& spec, 
                    const Dag& dag, 
                    chain<Dag::NrFanin>& chain)
            {
                fanin op_inputs[Dag::NrFanin];

                chain.reset(spec.get_nr_in(), 1, dag.get_nr_vertices());

                for (int i = 0; i < dag.get_nr_vertices(); i++) {
                    kitty::static_truth_table<Dag::NrFanin> op;
                    for (int j = 1; j <= nr_op_vars_per_step; j++) {
                        if (solver_var_value(*solver, get_op_var(dag, i, j))) {
                            kitty::set_bit(op, j); 
                        }
                    }

                    if (spec.verbosity) {
                        printf("  step x_%d performs operation\n  ", 
                                i+spec.get_nr_in()+1);
                        kitty::print_binary(op, std::cout);
                        printf("\n");
                    }

                    const auto& v = dag.get_vertex(i);
                    dag.foreach_fanin(v, [&op_inputs](auto f_id, int j) {
                        op_inputs[j] = f_id;
                    });
                    chain.set_step(i, op_inputs, op);
                        
                    if (spec.verbosity) {
                        printf("\n");
                    }
                }


                // TODO: support multiple outputs
                chain.set_output(0, 
                        ((dag.get_nr_vertices() + spec.get_nr_in()) << 1) +
                        ((spec.out_inv) & 1));

                /*
                auto triv_count = 0, nontriv_count = 0;
                for (int h = 0; h < spec.get_nr_out(); h++) {
                    if ((spec.triv_flag >> h) & 1) {
                        chain.set_output(h, (spec.triv_functions[triv_count++] << 1) +
                                ((spec.out_inv >> h) & 1));
                        continue;
                    }
                    for (int i = 0; i < spec.nr_steps; i++) {
                        if (solver_var_value(this->solver, 
                                    get_out_var(spec, nontriv_count, i))) {
                            chain.set_output(h, ((i + spec.get_nr_in() + 1) << 1) +
                                    ((spec.out_inv >> h) & 1));
                            nontriv_count++;
                            break;
                        }
                    }
                }
                */
            }

            // Assumes that a solution was found by the synthesizer. In that
            // case, we can block the current solution by blocking the current
            // assignment to the operator variables.
            void
            block_solution()
            {
                // TODO: implement
            }
    };
}

