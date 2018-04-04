#pragma once

#include "encoder_base.hpp"

namespace percy
{
    template<int FI=2, typename Solver=sat_solver*>
    class knuth_encoder
    {
        private:
            Solver& solver;

			int nr_op_vars_per_step;
			int nr_op_vars;
			int nr_out_vars;
			int nr_sim_vars;
			int nr_sel_vars;
            int sel_offset;
            int steps_offset;
            int out_offset;
            int sim_offset;
            
            abc::Vec_Int_t* vLits; // Dynamic vector of literals
            std::vector<std::array<int, FI>> svar_map;
            std::vector<int> nr_svar_map;

        public:
            knuth_encoder()
            {
                vLits = abc::Vec_IntAlloc(128);
            }

            ~knuth_encoder()
            {
                abc::Vec_IntFree(vLits);
            }

            void
            set_solver(Solver& s)
            {
                solver = s;
            }

            template<typename TT>
            int
            get_op_var(const synth_spec<TT>& spec, int step_idx, int var_idx) const
            {
                assert(step_idx < spec.nr_steps);
                assert(var_idx < nr_op_vars_per_step);

                return steps_offset + step_idx * nr_op_vars_per_step + var_idx;
            }

            int
            get_sel_var(int var_idx) const
            {
                assert(var_idx < nr_sel_vars);

                return sel_offset + var_idx;
            }

            template<typename TT>
            int 
            get_out_var(const synth_spec<TT>& spec, int h, int i) const
            {
                assert(h < spec.nr_nontriv);
                assert(i < spec.nr_steps);

                return out_offset + spec.nr_steps * h + i;
            }

            template<typename TT>
            int
            get_sim_var(const synth_spec<TT>& spec, int step_idx, int t) const
            {
                assert(step_idx < spec.nr_steps);
                assert(t < spec.get_tt_size());

                return nr_op_vars + spec.get_tt_size() * step_idx + t;
            }

            /*******************************************************************
                Ensures that each gate has FI operands.
            *******************************************************************/
            template<typename TT>
            void 
            create_op_clauses(const synth_spec<TT>& spec)
            {
                auto svar_offset = 0;
                for (int i = 0; i < spec.nr_steps; i++) {
                    const auto nr_svars_for_i = nr_svar_map[i];
                    
                    for (int j = 0; j < nr_svars_for_i; j++) {
                        abc::Vec_IntSetEntry(vLits, j,
                                abc::Abc_Var2Lit(get_sel_var(j + svar_offset),
                                    0));
                    }

                    solver_add_clause(solver, abc::Vec_IntArray(vLits), 
                            abc::Vec_IntArray(vLits) + nr_svars_for_i);

                    svar_offset += nr_svars_for_i;
                }
            }

            template<typename TT>
            void 
            create_output_clauses(const synth_spec<TT>& spec)
            {
                // Every output points to an operand.
                if (spec.nr_nontriv > 1) {
                    for (int h = 0; h < spec.nr_nontriv; h++) {
                        for (int i = 0; i < spec.nr_steps; i++) {
                            abc::Vec_IntSetEntry(vLits, i, 
                                    abc::Abc_Var2Lit(get_out_var(spec, h, i), 0));
                            if (spec.verbosity) {
                                printf("  output %d may point to step %d\n", 
                                        h+1, spec.get_nr_in()+i+1);
                            }
                        }
                        solver_add_clause(solver,abc::Vec_IntArray(vLits), 
                                abc::Vec_IntArray(vLits) + spec.nr_steps);
                    }
                }

                // At least one of the outputs has to refer to the final
                // operator, otherwise it may as well not be there.
                const auto last_op = spec.nr_steps - 1;
                for (int h = 0; h < spec.nr_nontriv; h++) {
                    abc::Vec_IntSetEntry(vLits, h, 
                            abc::Abc_Var2Lit(get_out_var(spec, h, last_op), 0));
                }
                solver_add_clause(solver, abc::Vec_IntArray(vLits), 
                        abc::Vec_IntArray(vLits) + spec.nr_nontriv);
            }

            template<typename TT>
            void
            create_variables(const synth_spec<TT>& spec)
            {
                std::array<int, FI> fanins;

                nr_op_vars_per_step = ((1u << FI) - 1);
                nr_op_vars = spec.nr_steps * nr_op_vars_per_step;
                nr_out_vars = spec.nr_nontriv * spec.nr_steps;
                nr_sim_vars = spec.nr_steps * spec.get_tt_size();

                nr_sel_vars = 0;
                svar_map.clear();
                nr_svar_map.resize(spec.nr_steps);
                for (int i = spec.get_nr_in(); 
						i < spec.get_nr_in() + spec.nr_steps; i++) {
                    //spec.nr_sel_vars += binomial_coeff(i, FI); 
					//( i * ( i - 1 ) ) / 2;
                    auto nr_svars_for_i = 0;
                    fanin_init<FI>(fanins, FI-1);
                    do  {
                        svar_map.push_back(fanins);
                        nr_svars_for_i++;
                    } while (fanin_inc<FI>(fanins, i-1));

                    nr_sel_vars += nr_svars_for_i;
                    nr_svar_map[i] = nr_svars_for_i;
                    assert(nr_svars_for_i = binomial_coeff(i ,FI));
                }
                sel_offset = 0;
                steps_offset = nr_sel_vars;
                out_offset = nr_sel_vars + nr_op_vars;
                sim_offset = nr_sel_vars + nr_op_vars + nr_out_vars;

                solver_set_nr_vars(solver, nr_op_vars + nr_out_vars +
                        nr_sim_vars + nr_sel_vars);
            }

            template<typename TT>
            bool 
            create_tt_clauses(const synth_spec<TT>& spec, int t)
            {
                auto ret = true;
                std::bitset<FI> fanin_asgn;
                int pLits[2];

                int sv_offst = 0;
                for (int i = 0; i < spec.nr_steps; i++) {
                    auto ctr = 0;
                    const auto nr_svars_for_i = nr_svar_map[i];

                    for (int j = sv_offst; j < sv_offst + nr_svars_for_i; j++) {
                        const auto& fanins = svar_map[j];
                        // First add clauses for all cases where the
                        // operator i computes zero.
                        int opvar_idx = 0;
                        clear_assignment<FI>(fanin_asgn);
                        while (true) {
                            next_assignment<FI>(fanin_asgn);
                            if (is_zero<FI>(fanin_asgn)) {
                                break;
                            }
                            opvar_idx++;
                            ret &= add_simulation_clause(spec, t, i, j, 0,
                                    opvar_idx, fanins, fanin_asgn);
                        }

                        // Next, all cases where operator i computes one.
                        opvar_idx = 0;
                        ret &= add_simulation_clause(spec, t, i, j, 1,
                                opvar_idx, fanins, fanin_asgn);
                        while (true) {
                            next_assignment<FI>(fanin_asgn);
                            if (is_zero<FI>(fanin_asgn)) {
                                break;
                            }
                            opvar_idx++;
                            ret &= add_simulation_clause(spec, t, i, j, 1,
                                    opvar_idx, fanins, fanin_asgn);
                        }
                    }
                    sv_offst += nr_svars_for_i;

                    // If an output has selected this particular operand, we
                    // need to ensure that this operand's truth table satisfies
                    // the specified output function.
                    for (int h = 0; h < spec.nr_nontriv; h++) {
                        auto outbit = kitty::get_bit(
                                *spec.functions[spec.synth_functions[h]], t+1);
                        if ((spec.out_inv >> spec.synth_functions[h]) & 1) {
                            outbit = 1 - outbit;
                        }
                        pLits[0] = abc::Abc_Var2Lit(get_out_var(spec, h, i), 1);
                        pLits[1] = abc::Abc_Var2Lit(get_sim_var(spec, i, t), 
                                1 - outbit);
                        ret &= solver_add_clause(solver, pLits, pLits+2);
                        if (spec.verbosity > 1) {
                            printf("  (g_%d_%d --> %sx_%d_%d)\n", h+1, 
                                    spec.get_nr_in()+i+1, 
                                    (1 - outbit) ?  "!" : "",
                                    spec.get_nr_in()+i+1, t+1);
                        }
                    }
                }

                return ret;
            }

            template<typename TT>
            bool 
            create_main_clauses(const synth_spec<TT>& spec)
            {
                auto success = true;

                for (int t = 0; t < spec.get_tt_size(); t++) {
                    success &= create_tt_clauses(spec, t);
                }

                return success;
            }

            template<typename TT>
            bool 
            add_simulation_clause(
                    const synth_spec<TT>& spec, 
                    int t, int i, int svar, int output, int opvar_idx,
                    auto fanins,
                    const std::bitset<FI>& fanin_asgn)
            {
                int ctr = 0;

                for (int j = 0; j < FI; j++) {
                    auto child = fanins[j];
                    auto assign = fanin_asgn[j];
                    if (child < spec.get_nr_in()) {
                        if ((((t + 1) & (1 << child) ) ? 1 : 0 ) != assign) {
                            return true;
                        }
                    } else {
                        abc::Vec_IntSetEntry(vLits, ctr++, abc::Abc_Var2Lit(
                                    get_sim_var(spec, child - spec.get_nr_in(),
                                        t), assign));
                    }
                }

                abc::Vec_IntSetEntry(vLits, ctr++,
                        abc::Abc_Var2Lit(get_sel_var(svar), 1));
                abc::Vec_IntSetEntry(vLits, ctr++,
                        abc::Abc_Var2Lit(get_sim_var(spec, i, t), output));

                if (opvar_idx > 0) {
                    abc::Vec_IntSetEntry(vLits, ctr++, abc::Abc_Var2Lit(
                                get_op_var(spec, i, opvar_idx), 1 - output));
                }

                return solver_add_clause(solver, abc::Vec_IntArray(vLits),
                        abc::Vec_IntArray(vLits) + ctr); 
            }

            /*******************************************************************
                Add clauses that prevent trivial variable projection and
                constant operators from being synthesized.
            *******************************************************************/
            template<typename TT>
            void 
            create_nontriv_clauses(const synth_spec<TT>& spec)
            {
                static_truth_table<FI> triv_op;

                for (int i = 0; i < spec.nr_steps; i++) {
                    kitty::clear(triv_op);
                    
                    // Dissallow the constant zero operator.
                    for (int j = 0; j < nr_op_vars_per_step; j++) {
                        abc::Vec_IntSetEntry(vLits, j,
                                abc::Abc_Var2Lit(get_op_var(spec, i, j), 
                                kitty::get_bit(triv_op, j+1)));
                    }
                    solver_add_clause(solver, abc::Vec_IntArray(vLits),
                            abc::Vec_IntArray(vLits) + nr_op_vars_per_step);
                    
                    // Dissallow all variable projection operators.
                    for (int n = 0; n < FI; i++) {
                        kitty::create_nth_var(triv_op, n);
                        for (int j = 0; j < nr_op_vars_per_step; j++) {
                            abc::Vec_IntSetEntry(vLits, j,
                                    abc::Abc_Var2Lit(get_op_var(spec, i, j), 
                                        kitty::get_bit(triv_op, j+1)));
                        }
                        solver_add_clause(solver, abc::Vec_IntArray(vLits),
                                abc::Vec_IntArray(vLits) + nr_op_vars_per_step);
                    }
                }
            }

            /*******************************************************************
              Add clauses which ensure that every step is used at least once.
            *******************************************************************/
/*
            template<typename TT>
            void 
            create_alonce_clauses(const synth_spec<TT>& spec)
            {
                for (int i = 0; i < spec.nr_steps; i++) {
                    auto ctr = 0;
                    for (int h = 0; h < spec.nr_nontriv; h++) {
                        abc::Vec_IntSetEntry(vLits, ctr++, 
                                abc::Abc_Var2Lit(get_out_var(spec, h, i), 0));
                    }
                    for (int ip = i + 1; ip < spec.nr_steps; ip++) {
                        for (int j = 0; j < spec.get_nr_in()+i; j++) {
                            abc::Vec_IntSetEntry(vLits, ctr++,
                                    abc::Abc_Var2Lit(
                                    get_sel_var(spec, ip, j, spec.get_nr_in()+i), 0));
                        }
                        for (int j = spec.get_nr_in()+i+1; j < spec.get_nr_in()+ip; j++) {
                            abc::Vec_IntSetEntry(vLits, ctr++, 
                                    abc::Abc_Var2Lit(
                                    get_sel_var(spec, ip, spec.get_nr_in()+i, j), 0));
                        }
                    }
                    solver_add_clause(this->solver, 
                            abc::Vec_IntArray(vLits),
                            abc::Vec_IntArray(vLits) + ctr);
                }
            }
*/

            /*******************************************************************
                Add clauses which ensure that operands are never re-applied. In
                other words, (Sijk --> ~Si'ji) & (Sijk --> ~Si'ki), 
                for all (i < i').
            *******************************************************************/
/*
            template<typename TT>
            void 
            create_noreapply_clauses(const synth_spec<TT>& spec)
            {
                int pLits[2];

                for (int i = 0; i < spec.nr_steps; i++) {
                    for (int ip = i+1; ip < spec.nr_steps; ip++) {
                        for (int k = 1; k < spec.get_nr_in()+i; k++) {
                            for (int j = 0; j < k; j++) {
                                pLits[0] = abc::Abc_Var2Lit(
                                        get_sel_var(spec, i, j, k), 1);
                                pLits[1] = abc::Abc_Var2Lit(
                                        get_sel_var(spec,ip,j,spec.get_nr_in()+i),1);
                                solver_add_clause(this->solver,pLits,pLits+2);
                                pLits[1] = abc::Abc_Var2Lit(
                                        get_sel_var(spec,ip,k,spec.get_nr_in()+i),1);
                                solver_add_clause(this->solver,pLits,pLits+2);
                            }
                        }
                    }
                }
            }
*/

            /*******************************************************************
                Add clauses which ensure that steps occur in co-lexicographic
                order. In other words, we require steps operands to be ordered
                tuples.
            *******************************************************************/
/*
            template<typename TT>
            void 
            create_colex_clauses(const synth_spec<TT>& spec)
            {
                int pLits[2];

                for (int i = 0; i < spec.nr_steps-1; i++) {
                    for (int k = 2; k < spec.get_nr_in()+i; k++) {
                        for (int j = 1; j < k; j++) {
                            for (int jp = 0; jp < j; jp++) {
                                pLits[0] = abc::Abc_Var2Lit(
                                        get_sel_var(spec, i, j, k), 1);
                                pLits[1] = abc::Abc_Var2Lit(
                                        get_sel_var(spec, i+1, jp, k), 1);
                                solver_add_clause(this->solver,pLits,pLits+2);
                            }
                        }
                        for (int j = 0; j < k; j++) {
                            for (int kp = 1; kp < k; kp++) {
                                for (int jp = 0; jp < kp; jp++) {
                                    pLits[0] = abc::Abc_Var2Lit(
                                            get_sel_var(spec, i, j, k), 1);
                                    pLits[1] = abc::Abc_Var2Lit(
                                            get_sel_var(spec, i+1, jp, kp),1);
                                    solver_add_clause(
                                            this->solver, pLits, pLits+2);
                                }
                            }
                        }
                    }
                }
            }
*/

            /*******************************************************************
                Ensure that Boolean operators are co-lexicographically ordered:
                (S_ijk == S_(i+1)jk) ==> f_i <= f_(i+1)
            *******************************************************************/
/*
            template<typename TT>
            void 
            create_colex_func_clauses(const synth_spec<TT>& spec)
            {
                int pLits[6];

                for (int i = 0; i < spec.nr_steps-1; i++) {
                    for (int k = 1; k < spec.get_nr_in()+i; k++) {
                        for (int j = 0; j < k; j++) {
                            pLits[0] = 
                                abc::Abc_Var2Lit(get_sel_var(spec, i, j, k), 1);
                            pLits[1] = 
                                abc::Abc_Var2Lit(get_sel_var(spec, i+1, j, k), 1);

                            pLits[2] = 
                                abc::Abc_Var2Lit(get_op_var(spec, i, 1, 1), 1);
                            pLits[3] = 
                                abc::Abc_Var2Lit(get_op_var(spec, i+1, 1, 1), 0);
                            solver_add_clause(this->solver, pLits, pLits+4);

                            pLits[3] = 
                                abc::Abc_Var2Lit(get_op_var(spec, i, 1, 0), 1);
                            pLits[4] = 
                                abc::Abc_Var2Lit(get_op_var(spec, i+1, 1, 1), 0);
                            solver_add_clause(this->solver, pLits, pLits+5);
                            pLits[4] = 
                                abc::Abc_Var2Lit(get_op_var(spec, i+1, 1, 0), 0);
                            solver_add_clause(this->solver, pLits, pLits+5);

                            pLits[4] = 
                                abc::Abc_Var2Lit(get_op_var(spec, i, 0, 1), 1);
                            pLits[5] = 
                                abc::Abc_Var2Lit(get_op_var(spec, i+1, 1, 1), 0);
                            solver_add_clause(this->solver, pLits, pLits+6);
                            pLits[5] = 
                                abc::Abc_Var2Lit(get_op_var(spec, i+1, 1, 0), 0);
                            solver_add_clause(this->solver, pLits, pLits+6);
                            pLits[5] = 
                                abc::Abc_Var2Lit(get_op_var(spec, i+1, 0, 1), 0);
                            solver_add_clause(this->solver, pLits, pLits+6);
                        }
                    }
                }
            }
*/

            /*******************************************************************
                Ensure that symmetric variables occur in order.
            *******************************************************************/
/*
            template<typename TT>
            void
            create_symvar_clauses(const synth_spec<TT>& spec)
            {
                for (int q = 1; q < spec.get_nr_in(); q++) {
                    for (int p = 0; p < q; p++) {
                        auto symm = true;
                        for (int i = 0; i < spec.nr_out; i++) {
                            auto outfunc = spec.functions[i];
                            if (!(swap(*outfunc, p, q) == *outfunc)) {
                                symm = false;
                                break;
                            }
                        }
                        if (!symm) {
                            continue;
                        }
                        if (spec.verbosity) {
                            printf("  variables x_%d and x_%d are symmetric\n",
                                    p+1, q+1);
                        }
                        for (int i = 0; i < spec.nr_steps; i++) {
                            for (int j = 0; j < q; j++) {
                                if (j == p) continue;

                                auto slit = 
                                    abc::Abc_Var2Lit(get_sel_var(spec, i, j, q), 1);
                                abc::Vec_IntSetEntry(vLits, 0, slit);

                                int ctr = 1;
                                for (int ip = 0; ip < i; ip++) {
                                    for (int kp = 1; kp < spec.get_nr_in()+ip; kp++) {
                                        for (int jp = 0; jp < kp; jp++) {
                                            if (jp == p || kp == p) {
                                                slit = abc::Abc_Var2Lit(
                                                            get_sel_var(spec, 
                                                            ip, jp, kp), 0);
                                                abc::Vec_IntSetEntry(vLits, 
                                                        ctr++, slit);
                                                solver_add_clause(
                                                    this->solver, 
                                                    abc::Vec_IntArray(vLits),
                                                    abc::Vec_IntArray(vLits) +
                                                    ctr);
                                            }
                                        }
                                    }
                                }
                            }
                        }
                    }
                }
            }
*/

            /*******************************************************************
              Extracts a Boolean chain from a satisfiable solution.
            *******************************************************************/
            template<typename TT>
            void 
            extract_chain(synth_spec<TT>& spec, chain<FI>& chain)
            {
                int op_inputs[2];

                chain.reset(spec.get_nr_in(), spec.get_nr_out(), spec.nr_steps);

                auto svar_offset = 0;
                for (int i = 0; i < spec.nr_steps; i++) {
                    kitty::static_truth_table<FI> op;
                    for (int j = 0; j < nr_op_vars_per_step; j++) {
                        if (solver_var_value(solver, get_op_var(spec, i, j))) {
                            kitty::set_bit(op, j + 1); 
                        }
                    }

                    if (spec.verbosity) {
                        printf("  step x_%d performs operation\n  ", 
                                i+spec.get_nr_in()+1);
                        kitty::print_binary(op, std::cout);
                        printf("\n");
                    }

                    const auto nr_svars_for_i = nr_svar_map[i];
                    for (int j = 0; j < nr_svars_for_i; j++) {
                        const auto sel_var = get_sel_var(svar_offset + j);
                        if (solver_var_value(solver, sel_var)) {
                            const auto& fanins = svar_map[svar_offset + j];
                            if (spec.verbosity) {
                                printf("  with operands ");
                                for (int k = 0; k < FI; k++) {
                                    printf("x_%d ", fanins[k] + 1);
                                }
                            }
                            chain.set_step(i, fanins, op);
                            break;
                        }
                    }

                    svar_offset += nr_svars_for_i;

                    if (spec.verbosity) {
                        printf("\n");
                    }
                }

                auto triv_count = 0, nontriv_count = 0;
                for (int h = 0; h < spec.get_nr_out(); h++) {
                    if ((spec.triv_flag >> h) & 1) {
                        chain.set_output(h, 
                                (spec.triv_functions[triv_count++] << 1) +
                                ((spec.out_inv >> h) & 1));
                        continue;
                    }
                    for (int i = 0; i < spec.nr_steps; i++) {
                        if (solver_var_value(solver, 
                                    get_out_var(spec, nontriv_count, i))) {
                            chain.set_output(h, ((i + spec.get_nr_in() + 1) << 1) +
                                    ((spec.out_inv >> h) & 1));
                            nontriv_count++;
                            break;
                        }
                    }
                }
            }

            /*******************************************************************
                Extracts only the underlying DAG structure from a solution.
            *******************************************************************/
            template<typename TT>
            void 
            extract_dag(synth_spec<TT>& spec, dag<FI>& dag)
            {
                dag.reset(spec.get_nr_in(), spec.nr_steps);

                for (int i = 0; i < spec.nr_steps; i++) {
                    for (int k = 1; k < spec.get_nr_in() + i; k++) {
                        for (int j = 0; j < k; j++) {
                            if (solver_var_value(solver,
                                        get_sel_var(spec, i, j, k)))
                            {
                                dag.set_vertex(i, j, k);
                                break;
                            }

                        }
                    }
                }
            }

            template<typename TT>
            void
            print_solver_state(const synth_spec<TT>& spec)
            {
                printf("\n");
                printf("========================================"
                        "========================================\n");
                printf("  SOLVER STATE\n\n");

                for (int i = 0; i < spec.nr_steps; i++) {
                    for (int k = 1; k < spec.get_nr_in()+i; k++) {
                        for (int j = 0; j < k; j++) {
                            if (solver_var_value(solver, 
                                        get_sel_var(spec, i, j, k))) {
                                printf("  x_%d has inputs x_%d and x_%d\n",
                                        spec.get_nr_in()+i+1, j+1, k+1);
                            }
                        }
                    }
                    printf("  f_%d = ", spec.get_nr_in()+i+1);
                    printf("%d", solver_var_value(solver, 
                                get_op_var(spec, i, 1, 1)));
                    printf("%d", solver_var_value(solver, 
                                get_op_var(spec, i, 1, 0)));
                    printf("%d", solver_var_value(solver, 
                                get_op_var(spec, i, 0, 1)));
                    printf("0\n");
                    printf("  tt_%d = ",spec.get_nr_in()+ i+1);
                    for (int t = spec.get_tt_size() - 1; t >= 0; t--) {
                        printf("%d", solver_var_value(solver, 
                                    get_sim_var(spec, i, t)));
                    }
                    printf("0\n\n");
                }

                for (int h = 0; h < spec.nr_nontriv; h++) {
                    for (int i = 0; i < spec.nr_steps; i++) {
                        if (solver_var_value(solver, get_out_var(spec,h,i))) {
                            printf("  g_%d --> x_%d\n", h+1, spec.get_nr_in()+i+1);
                        }
                    }
                }

                for (int h = 0; h < spec.nr_nontriv; h++) {
                    for (int i = 0; i < spec.nr_steps; i++) {
                        printf("  g_%d_%d=%d\n", h+1, spec.get_nr_in()+i+1,
                                solver_var_value(solver, get_out_var(spec, h, i))
                              );
                    }
                }
                printf("\n");

                for (int i = 0; i < spec.nr_steps; i++) {
                    for (int k = 1; k < spec.get_nr_in()+i; k++) {
                        for (int j = 0; j < k; j++) {
                            printf("s_%d_%d_%d=%d\n", spec.get_nr_in()+i+1, j+1, k+1,
                                    solver_var_value(solver, 
                                        get_sel_var(spec, i, j, k)));
                        }
                    }
                    printf("\n");
                    printf("f_%d_0_0=0\n", spec.get_nr_in()+i+1);
                    printf("f_%d_0_1=%d\n", spec.get_nr_in()+i+1, 
                            solver_var_value(solver, 
                                get_op_var(spec, i, 0, 1)));
                    printf("f_%d_1_0=%d\n", spec.get_nr_in()+i+1, 
                            solver_var_value(solver,
                                get_op_var(spec, i, 1, 0)));
                    printf("f_%d_1_1=%d\n", spec.get_nr_in()+i+1, 
                            solver_var_value(solver, 
                                get_op_var(spec, i, 1, 1)));
                    printf("\n");
                    for (int t = spec.get_tt_size() - 1; t >= 0; t--) {
                        printf("x_%d_%d=%d\n", spec.get_nr_in()+i+1, t+1, 
                                solver_var_value(solver, 
                                    get_sim_var(spec, i, t)));
                    }
                    printf("x_%d_0=0\n", spec.get_nr_in()+i);
                    printf("\n");
                }
                printf("\n");

                printf("========================================"
                        "========================================\n");
            }

            template<typename TT>
            bool 
            encode(const synth_spec<TT>& spec)
            {
                assert(spec.nr_steps <= MAX_STEPS);

                create_variables(spec);
                const auto success = create_main_clauses(spec);
                if (!success) {
                    return false;
                }

                create_output_clauses(spec);
                create_op_clauses(spec);

                if (spec.add_nontriv_clauses) {
                    create_nontriv_clauses(spec);
                }
                /*
                if (spec.add_alonce_clauses) {
                    create_alonce_clauses(spec);
                }
                if (spec.add_noreapply_clauses) {
                    create_noreapply_clauses(spec);
                }
                if (spec.add_colex_clauses) {
                    create_colex_clauses(spec);
                }
                if (spec.add_colex_func_clauses) {
                    create_colex_func_clauses(spec);
                }
                if (spec.add_symvar_clauses) {
                    create_symvar_clauses(spec);
                }
                */

                return true;
            }

            template<typename TT>
            bool 
            cegar_encode(const synth_spec<TT>& spec)
            {
                assert(spec.nr_steps <= MAX_STEPS);

                create_variables(spec);
                for (int i = 0; i < spec.nr_rand_tt_assigns; i++) {
                    if (!create_tt_clauses(spec, rand()%spec.get_tt_size())) {
                        return false;
                    }
                }
                
                create_output_clauses(spec);
                create_op_clauses(spec);

                if (spec.add_nontriv_clauses) {
                    create_nontriv_clauses(spec);
                }
                /*
                if (spec.add_alonce_clauses) {
                    create_alonce_clauses(spec);
                }
                if (spec.add_noreapply_clauses) {
                    create_noreapply_clauses(spec);
                }
                if (spec.add_colex_clauses) {
                    create_colex_clauses(spec);
                }
                if (spec.add_colex_func_clauses) {
                    create_colex_func_clauses(spec);
                }
                if (spec.add_symvar_clauses) {
                    create_symvar_clauses(spec);
                }
                */

                return true;
            }
    };
}

