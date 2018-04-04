#pragma once

#include "encoder_base.hpp"

namespace percy
{
    template<typename Dag, typename Solver=sat_solver*>
    class dag_encoder
    {
        private:
            // We only keep a reference to the solver. Since we don't own it,
            // we should never use encoders outside of the synthesizer objects
            // that own them and the solvers.
            Solver& solver;

            int nr_op_vars;
            int nr_sim_vars;
            int verbosity;
            int nr_op_vars_per_step;
            int tt_size;
            int nr_vertices;
            int nr_inputs;
            
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
            set_solver(Solver& s)
            {
                solver = s;
            }

            int
            get_op_var(int step_idx, int var_idx)
            {
                assert(step_idx < nr_vertices);
                assert(var_idx < nr_op_vars_per_step);

                return step_idx * nr_op_vars_per_step + var_idx;
            }

            int
            get_sim_var(int step_idx, int t)
            {
                assert(step_idx < nr_vertices);

                return nr_op_vars + tt_size * step_idx + t;
            }

            void 
            set_verbosity(int v)
            {
                verbosity = v;
            }

            template<typename TT>
            void
            create_variables(const synth_spec<TT>& spec, const Dag& dag)
            {
                nr_vertices = dag.get_nr_vertices();
                tt_size = spec.get_tt_size();
                nr_inputs = spec.get_nr_in();

                nr_op_vars_per_step = ((1u << Dag::NrFanin) - 1);
                nr_op_vars = nr_vertices * nr_op_vars_per_step;
                nr_sim_vars = nr_vertices * tt_size;
                if (verbosity > 1) {
                    printf("nr_op_vars=%d\n", nr_op_vars);
                    printf("nr_sim_vars=%d\n", nr_sim_vars);
                }


                solver_set_nr_vars(solver, nr_op_vars + nr_sim_vars);
            }

            bool
            add_simulation_clause(int t, int i, int output, int opvar_idx,
                    auto fanins,
                    const std::bitset<Dag::NrFanin>& fanin_asgn)
            {
                int ctr = 0;

                for (int j = 0; j < Dag::NrFanin; j++) {
                    auto child = fanins[j];
                    auto assign = fanin_asgn[j];
                    if (child < nr_inputs) {
                        if (( ( (t + 1) & (1 << child) ) ? 1 : 0 ) != assign) {
                            return true;
                        }
                    } else {
                        abc::Vec_IntSetEntry(vLits, ctr++, abc::Abc_Var2Lit(
                                    get_sim_var(child - nr_inputs, t), assign));
                    }
                }

                abc::Vec_IntSetEntry(vLits, ctr++,
                        abc::Abc_Var2Lit(get_sim_var(i, t), output));

                if (opvar_idx > 0) {
                    abc::Vec_IntSetEntry(vLits, ctr++, abc::Abc_Var2Lit(
                                get_op_var(i, opvar_idx), 1 - output));
                }

                return solver_add_clause(solver, abc::Vec_IntArray(vLits),
                        abc::Vec_IntArray(vLits) + ctr); 
            }

            template<typename TT>
            bool
            create_tt_clauses(const synth_spec<TT>& spec, const Dag& dag, int t)
            {
                auto ret = true;
                fanin<Dag> fanins[Dag::NrFanin];
                std::bitset<Dag::NrFanin> fanin_asgn;


                for (int i = 0; i < nr_vertices && ret; i++) {
                    auto v = dag.get_vertex(i);
                    dag.foreach_fanin(v, [&fanins] (auto f_id, int j) {
                        fanins[j] = f_id;
                    });

                    // First add clauses for all cases where the operator i
                    // computes zero.
                    clear_assignment<Dag::NrFanin>(fanin_asgn);
                    int opvar_idx = 0;
                    while (true) {
                        next_assignment<Dag::NrFanin>(fanin_asgn);
                        if (is_zero<Dag::NrFanin>(fanin_asgn)) {
                            break;
                        }
                        opvar_idx++;
                        ret &= add_simulation_clause(t, i, 0, opvar_idx,
                                fanins, fanin_asgn);
                    }

                    // Next, all cases where operator i computes one.
                    opvar_idx = 0;
                    ret &= add_simulation_clause(t, i, 1, opvar_idx, fanins,
                            fanin_asgn);
                    while (true) {
                        next_assignment<Dag::NrFanin>(fanin_asgn);
                        if (is_zero<Dag::NrFanin>(fanin_asgn)) {
                            break;
                        }
                        opvar_idx++;
                        ret &= add_simulation_clause(t, i, 1, opvar_idx,
                                fanins, fanin_asgn);
                    }

                    // If an output has selected this particular operand, we
                    // need to ensure that this operand's truth table satisfies
                    // the specified output function.
                    if (i == nr_vertices-1) {
                        int pLits[2];

                        if (verbosity > 1) {
                            printf("bit %d=%d", t+2, 
                                    kitty::get_bit(*spec.functions[0], t+1));
                            printf("\tvar=%d\n", get_sim_var(i, t));
                        }
                        auto outbit = kitty::get_bit(*spec.functions[0], t+1);
                        pLits[0] = abc::Abc_Var2Lit(get_sim_var(i, t), 
                                1 - outbit);
                        ret &= solver_add_clause(solver,pLits,pLits+1);
                    }
                }

                return ret;
            }

            template<typename TT>
            bool
            create_main_clauses(const synth_spec<TT>& spec, const Dag& dag)
            {
                for (int t = 0; t < tt_size; t++) {
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
                assert(spec.nr_steps <= MAX_STEPS);

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
                assert(spec.nr_steps <= MAX_STEPS);

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
                fanin<Dag> op_inputs[Dag::NrFanin];

                chain.reset(nr_inputs, 1, nr_vertices);

                auto svar_offset = 0;
                for (int i = 0; i < nr_vertices; i++) {
                    kitty::static_truth_table<Dag::NrFanin> op;
                    for (int j = 0; j < nr_op_vars_per_step; j++) {
                        if (solver_var_value(solver, get_op_var(i, j))) {
                            kitty::set_bit(op, j + 1); 
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
                    for (int k = 0; k < Dag::NrFanin; k++) {
                        printf("x_%d ", op_inputs[k] + 1);
                    }
                        
                    if (spec.verbosity) {
                        printf("\n");
                    }
                }


                // TODO: support multiple outputs
                chain.set_output(0, ((nr_vertices + nr_inputs) << 1) +
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

