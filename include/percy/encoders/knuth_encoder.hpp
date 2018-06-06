#pragma once

#include "encoder_base.hpp"
#include "../misc.hpp"

namespace percy
{
    using abc::Abc_Var2Lit;
    using abc::Vec_IntSetEntry;
    using abc::Vec_IntArray;

    template<int FI=2, typename Solver=sat_solver*>
    class knuth_encoder
    {
        using fanin = typename dag<FI>::fanin;

        private:
            Solver* solver;

			int nr_op_vars_per_step;
			int nr_op_vars;
			int nr_out_vars;
			int nr_sim_vars;
			int nr_sel_vars;
			int nr_lex_vars;
            int sel_offset;
            int ops_offset;
            int out_offset;
            int sim_offset;
            int lex_offset;
            int total_nr_vars;
            
            abc::Vec_Int_t* vLits; // Dynamic vector of literals
            std::vector<std::array<fanin, FI>> svar_map;
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
            set_solver(Solver* s)
            {
                solver = s;
            }

            template<typename TT>
            int
            get_op_var(const synth_spec<TT>& spec, int step_idx, int var_idx)
            const 
            {
                assert(step_idx < spec.nr_steps);
                assert(var_idx > 0);
                assert(var_idx <= nr_op_vars_per_step);

                return ops_offset + step_idx * nr_op_vars_per_step + var_idx-1;
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

                return sim_offset + spec.get_tt_size() * step_idx + t;
            }

            template<typename TT>
            int
            get_lex_var(const synth_spec<TT>& spec, int step_idx, int op_idx) const
            {
                assert(step_idx < spec.nr_steps);
                assert(op_idx < nr_op_vars_per_step);

                return lex_offset + step_idx * (nr_op_vars_per_step - 1) + op_idx;
            }

            /*******************************************************************
                Ensures that each gate has FI operands.
            *******************************************************************/
            template<typename TT>
            bool 
            create_op_clauses(const synth_spec<TT>& spec)
            {
                auto status = true;

                if (spec.verbosity > 2) {
                    printf("Creating op clauses (KNUTH-%d)\n", FI);
                    printf("Nr. clauses = %d (PRE)\n",
                            solver_nr_clauses(*solver));
                }

                auto svar_offset = 0;
                for (int i = 0; i < spec.nr_steps; i++) {
                    const auto nr_svars_for_i = nr_svar_map[i];
                    
                    for (int j = 0; j < nr_svars_for_i; j++) {
                        Vec_IntSetEntry(vLits, j, 
                                Abc_Var2Lit(get_sel_var(j + svar_offset), 0));
                    }

                    status &= solver_add_clause(
                            *solver,
                            abc::Vec_IntArray(vLits), 
                            abc::Vec_IntArray(vLits) + nr_svars_for_i);

                    if (spec.verbosity > 2) {
                        printf("creating op clause: ( ");
                        for (int j = 0; j < nr_svars_for_i; j++) {
                            printf("%ss_%d_%d ", j > 0 ? "\\/ " : "",
                                    spec.get_nr_in() + i + 1, j + 1);
                        }
                        printf(") (status=%d)\n", status);
                        for (int j = 0; j < nr_svars_for_i; j++) {
                            printf("svar(%d) = %d\n", j + svar_offset,
                                    get_sel_var(j + svar_offset));
                        }
                    }

                    svar_offset += nr_svars_for_i;
                }
                if (spec.verbosity > 2) {
                    printf("Nr. clauses = %d (POST)\n",
                            solver_nr_clauses(*solver));
                }

                return status;
            }

            template<typename TT>
            bool 
            create_output_clauses(const synth_spec<TT>& spec)
            {
                auto status = true;

                if (spec.verbosity > 2) {
                    printf("Creating output clauses (KNUTH-%d)\n", FI);
                    printf("Nr. clauses = %d (PRE)\n",
                            solver_nr_clauses(*solver));
                }
                // Every output points to an operand.
                if (spec.nr_nontriv > 1) {
                    for (int h = 0; h < spec.nr_nontriv; h++) {
                        for (int i = 0; i < spec.nr_steps; i++) {
                            abc::Vec_IntSetEntry(vLits, i, 
                                    abc::Abc_Var2Lit(get_out_var(spec, h, i), 0));
                        }
                        status &= solver_add_clause(
                                *solver,
                                abc::Vec_IntArray(vLits),
                                abc::Vec_IntArray(vLits) + spec.nr_steps);

                        if (spec.verbosity > 2) {
                            printf("creating output clause: ( ");
                            for (int i = 0; i < spec.nr_steps; i++) {
                                printf("%sg_%d_%d ", i > 0 ? "\\/ " : "",
                                        h + 1, spec.get_nr_in() + i + 1);
                            }
                            printf(") (status = %d)\n", status);
                        }
                    }
                }

                // At least one of the outputs has to refer to the final
                // operator, otherwise it may as well not be there.
                const auto last_op = spec.nr_steps - 1;
                for (int h = 0; h < spec.nr_nontriv; h++) {
                    abc::Vec_IntSetEntry(vLits, h,
                            abc::Abc_Var2Lit(get_out_var(spec, h, last_op),0));
                }
                status &= solver_add_clause(*solver, abc::Vec_IntArray(vLits), 
                        abc::Vec_IntArray(vLits) + spec.nr_nontriv);

                if (spec.verbosity > 2) {
                    printf("creating output clause: ( ");
                    for (int h = 0; h < spec.nr_nontriv; h++) {
                        printf("%sg_%d_%d ", h > 0 ? "\\/ " : "",
                                h + 1, spec.get_nr_in() + last_op + 1);
                    }
                    printf(") (status = %d)\n", status);
                    printf("Nr. clauses = %d (POST)\n",
                            solver_nr_clauses(*solver));
                }

                return status;
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
                nr_lex_vars = (spec.nr_steps - 1) * (nr_op_vars_per_step - 1);
                nr_sel_vars = 0;
                svar_map.clear();
                nr_svar_map.resize(spec.nr_steps);
                for (int i = spec.get_nr_in(); 
						i < spec.get_nr_in() + spec.nr_steps; i++) {
                    if (spec.verbosity > 2) {
                        printf("adding sel vars for step %d\n",
                                i + 1);
                    }
                    //spec.nr_sel_vars += binomial_coeff(i, FI); 
					//( i * ( i - 1 ) ) / 2;
                    auto nr_svars_for_i = 0;
                    fanin_init<FI>(fanins, FI-1);
                    do  {
                        if (spec.verbosity > 4) {
                            print_fanin(fanins);
                        }
                        svar_map.push_back(fanins);
                        nr_svars_for_i++;
                    } while (fanin_inc<FI>(fanins, i-1));
                    
                    if (spec.verbosity > 2) {
                        printf("added %d sel vars\n", nr_svars_for_i);
                    }

                    nr_sel_vars += nr_svars_for_i;
                    nr_svar_map[i - spec.get_nr_in()] = nr_svars_for_i;
                    assert(nr_svars_for_i == binomial_coeff(i, FI));
                }
                sel_offset = 0;
                ops_offset = nr_sel_vars;
                out_offset = nr_sel_vars + nr_op_vars;
                sim_offset = nr_sel_vars + nr_op_vars + nr_out_vars;
                lex_offset = nr_sel_vars + nr_op_vars + nr_out_vars + nr_sim_vars;
                
                total_nr_vars = nr_op_vars + nr_out_vars + nr_sim_vars +
                                nr_sel_vars + nr_lex_vars;

                if (spec.verbosity > 2) {
                    printf("Creating variables (KNUTH-%d)\n", FI);
                    printf("nr steps = %d\n", spec.nr_steps);
                    printf("nr_sel_vars=%d\n", nr_sel_vars);
                    printf("nr_op_vars = %d\n", nr_op_vars);
                    printf("nr_out_vars = %d\n", nr_out_vars);
                    printf("nr_sim_vars = %d\n", nr_sim_vars);
                    printf("nr_lex_vars = %d\n", nr_lex_vars);
                    printf("creating %d total variables\n", total_nr_vars);
                }

                solver_set_nr_vars(*solver, total_nr_vars);
            }

            template<typename TT>
            bool 
            create_tt_clauses(const synth_spec<TT>& spec, const int t)
            {
                auto ret = true;
                std::bitset<FI> fanin_asgn;
                int pLits[2];

                int svar_offset = 0;
                for (int i = 0; i < spec.nr_steps; i++) {
                    const auto nr_svars_for_i = nr_svar_map[i];

                    for (int j = 0; j < nr_svars_for_i; j++) {
                        const auto svar = j + svar_offset;
                        const auto& fanins = svar_map[svar];

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
                            ret &= add_simulation_clause(spec, t, i, svar, 0,
                                    opvar_idx, fanins, fanin_asgn);
                        }

                        // Next, all cases where operator i computes one.
                        opvar_idx = 0;
                        ret &= add_simulation_clause(spec, t, i, svar, 1,
                                opvar_idx, fanins, fanin_asgn);
                        while (true) {
                            next_assignment<FI>(fanin_asgn);
                            if (is_zero<FI>(fanin_asgn)) {
                                break;
                            }
                            opvar_idx++;
                            ret &= add_simulation_clause(spec, t, i, svar, 1,
                                    opvar_idx, fanins, fanin_asgn);
                        }
                    }
                    svar_offset += nr_svars_for_i;

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
                        ret &= solver_add_clause(*solver, pLits, pLits+2);
                        if (spec.verbosity > 2) {
                            printf("creating oimp clause: ( ");
                            printf("!g_%d_%d \\/ %sx_%d_%d ) (status=%d)\n", 
                                    h+1, 
                                    spec.get_nr_in() + i + 1, 
                                    (1 - outbit) ?  "!" : "",
                                    spec.get_nr_in() + i + 1, 
                                    t + 2,
                                    ret);
                        }
                    }
                }

                return ret;
            }

            template<typename TT>
            bool 
            create_main_clauses(const synth_spec<TT>& spec)
            {
                if (spec.verbosity > 2) {
                    printf("Creating main clauses (KNUTH-%d)\n", FI);
                    printf("Nr. clauses = %d (PRE)\n",
                            solver_nr_clauses(*solver));
                }
                auto success = true;

                for (int t = 0; t < spec.get_tt_size(); t++) {
                    success &= create_tt_clauses(spec, t);
                }

                if (spec.verbosity > 2) {
                    printf("Nr. clauses = %d (POST)\n",
                            solver_nr_clauses(*solver));
                }

                return success;
            }

            template<typename TT>
            bool 
            add_simulation_clause(
                    const synth_spec<TT>& spec, 
                    const int t, 
                    const int i, 
                    const int svar, 
                    const int output, 
                    const int opvar_idx,
                    const std::array<fanin, FI>& fanins,
                    const std::bitset<FI>& fanin_asgn)
            {
                int ctr = 0;

                if (spec.verbosity > 3) {
                    //printf("assignment: %s\n", fanin_asgn.to_string().c_str());
                }

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

                //printf("sel_var=%d, sim_var=%d\n", svar, get_sim_var(spec, i, t));

                //printf("opvar_idx=%d\n", opvar_idx);
                if (opvar_idx > 0) {
                    abc::Vec_IntSetEntry(vLits, ctr++, abc::Abc_Var2Lit(
                                get_op_var(spec, i, opvar_idx), 1 - output));
                }

                auto status = solver_add_clause(*solver,
                        abc::Vec_IntArray(vLits),
                        abc::Vec_IntArray(vLits) + ctr); 

                if (spec.verbosity > 2) {
                    printf("creating sim. clause: (");
                    printf(" !s_%d_%d ", spec.get_nr_in() + i + 1, svar + 1);
                    printf(" \\/ %sx_%d_%d ", output ? "!" : "", 
                            spec.get_nr_in() + i + 1, t + 2);

                    for (int j = 0; j < FI; j++) {
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
                    for (int j = 1; j <= nr_op_vars_per_step; j++) {
                        abc::Vec_IntSetEntry(vLits, j-1,
                                abc::Abc_Var2Lit(get_op_var(spec, i, j), 0));
                    }
                    auto status = solver_add_clause(*solver,
                            abc::Vec_IntArray(vLits), 
                            abc::Vec_IntArray(vLits) + nr_op_vars_per_step);
                    assert(status);
                    
                    // Dissallow all variable projection operators.
                    for (int n = 0; n < FI; n++) {
                        kitty::create_nth_var(triv_op, n);
                        for (int j = 1; j <= nr_op_vars_per_step; j++) {
                            abc::Vec_IntSetEntry(vLits, j-1,
                                    abc::Abc_Var2Lit(get_op_var(spec, i, j), 
                                        kitty::get_bit(triv_op, j)));
                        }
                        status = solver_add_clause(*solver, 
                                abc::Vec_IntArray(vLits),
                                abc::Vec_IntArray(vLits) + nr_op_vars_per_step);
                        assert(status);
                    }
                }
            }

            /*******************************************************************
              Add clauses which ensure that every step is used at least once.
            *******************************************************************/
            template<typename TT>
            void 
            create_alonce_clauses(const synth_spec<TT>& spec)
            {
                for (int i = 0; i < spec.nr_steps; i++) {
                    auto ctr = 0;

                    // Either one of the outputs points to this step.
                    for (int h = 0; h < spec.nr_nontriv; h++) {
                        abc::Vec_IntSetEntry(vLits, ctr++, 
                                abc::Abc_Var2Lit(get_out_var(spec, h, i), 0));
                    }

                    auto svar_offset = 0;
                    for (int j = 0; j < i + 1; j++) {
                        svar_offset += nr_svar_map[j];
                    }

                    // Or one of the succeeding steps points to this step.
                    for (int ip = i + 1; ip < spec.nr_steps; ip++) {
                        const auto nr_svars_for_ip = nr_svar_map[ip];
                        for (int j = 0; j < nr_svars_for_ip; j++) {
                            const auto sel_var = get_sel_var(svar_offset + j);
                            const auto& fanins = svar_map[svar_offset + j];
                            for (auto fanin : fanins) {
                                if (fanin == spec.get_nr_in() + i) {
                                    abc::Vec_IntSetEntry(
                                            vLits, 
                                            ctr++,
                                            abc::Abc_Var2Lit(
                                                get_sel_var(sel_var), 0)
                                    );
                                }
                            }
                        }
                        svar_offset += nr_svars_for_ip;
                    }
                    auto status = solver_add_clause(
                            *solver, 
                            abc::Vec_IntArray(vLits),
                            abc::Vec_IntArray(vLits) + ctr);
                    assert(status);
                }
            }

            /*******************************************************************
                Add clauses which ensure that operands are never re-applied. In
                other words, (Sijk --> ~Si'ji) & (Sijk --> ~Si'ki), 
                for all (i < i').
            *******************************************************************/
            template<typename TT>
            void 
            create_noreapply_clauses(const synth_spec<TT>& spec)
            {
                int pLits[2];
                auto svar_offset = 0;

                for (int i = 0; i < spec.nr_steps - 1; i++) {
                    const auto nr_svars_for_i = nr_svar_map[i];
                    for (int j = 0; j < nr_svars_for_i; j++) {
                        const auto sel_var = get_sel_var(svar_offset + j);
                        const auto& fanins = svar_map[svar_offset + j];
                        
                        auto svar_offsetp = 0;
                        for (int k = 0; k < i + 1; k++) {
                            svar_offsetp += nr_svar_map[k];
                        }

                        for (int ip = i + 1; ip < spec.nr_steps; ip++) {
                            const auto nr_svars_for_ip = nr_svar_map[ip];
                            for (int jp = 0; jp < nr_svars_for_ip; jp++) {
                                const auto sel_varp = 
                                    get_sel_var(svar_offsetp + jp);
                                const auto& faninsp = 
                                    svar_map[svar_offsetp + jp];

                                auto subsumed = true;
                                auto has_fanin_i = false;
                                for (auto faninp : faninsp) {
                                    if (faninp == i + spec.get_nr_in()) {
                                        has_fanin_i = true;
                                    } else {
                                        auto is_included = false;
                                        for (auto fanin : fanins) {
                                            if (fanin == faninp) {
                                                is_included = true;
                                            }
                                        }
                                        if (!is_included) {
                                            subsumed = false;
                                        }
                                    }
                                }
                                if (has_fanin_i && subsumed) {
                                    pLits[0] = Abc_Var2Lit(sel_var, 1);
                                    pLits[1] = Abc_Var2Lit(sel_varp, 1);
                                    auto status = solver_add_clause(
                                                    *solver, 
                                                    pLits,
                                                    pLits + 2);
                                    assert(status);
                                }
                            }

                            svar_offsetp += nr_svars_for_ip;
                        }
                    }
                    svar_offset += nr_svars_for_i;
                }
            }

            /*******************************************************************
                Add clauses which ensure that steps occur in co-lexicographical
                order. In other words, we require steps operands to be 
                co-lexicographically ordered tuples.
            *******************************************************************/
            template<typename TT>
            void 
            create_colex_clauses(const synth_spec<TT>& spec)
            {
                int pLits[2];
                auto svar_offset = 0;

                for (int i = 0; i < spec.nr_steps - 1; i++) {
                    const auto nr_svars_for_i = nr_svar_map[i];
                    for (int j = 0; j < nr_svars_for_i; j++) {
                        const auto sel_var = get_sel_var(svar_offset + j);
                        const auto& fanins1 = svar_map[svar_offset + j];
                        pLits[0] = Abc_Var2Lit(sel_var, 1);

                        auto svar_offsetp = svar_offset + nr_svars_for_i;
                        const auto nr_svars_for_ip = nr_svar_map[i + 1];
                        for (int jp = 0; jp < nr_svars_for_ip; jp++) {
                            const auto sel_varp = get_sel_var(svar_offsetp+jp);
                            const auto& fanins2 = svar_map[svar_offsetp + jp];

                            if (colex_compare<int, FI>(fanins1, fanins2) == 1) {
                                pLits[1] = Abc_Var2Lit(sel_varp, 1);
                                auto status = 
                                    solver_add_clause(*solver, pLits, pLits+2);
                                assert(status);
                            }
                        }
                    }

                    svar_offset += nr_svars_for_i;
                }
            }

            /*******************************************************************
                Add clauses which ensure that steps occur in lexicographical
                order. In other words, we require steps operands to be
                lexicographically ordered tuples.
            *******************************************************************/
            template<typename TT>
            void 
            create_lex_clauses(const synth_spec<TT>& spec)
            {
                int pLits[2];
                auto svar_offset = 0;

                for (int i = 0; i < spec.nr_steps - 1; i++) {
                    const auto nr_svars_for_i = nr_svar_map[i];
                    for (int j = 0; j < nr_svars_for_i; j++) {
                        const auto sel_var = get_sel_var(svar_offset + j);
                        const auto& fanins1 = svar_map[svar_offset + j];
                        pLits[0] = Abc_Var2Lit(sel_var, 1);

                        auto svar_offsetp = svar_offset + nr_svars_for_i;
                        const auto nr_svars_for_ip = nr_svar_map[i + 1];
                        for (int jp = 0; jp < nr_svars_for_ip; jp++) {
                            const auto sel_varp = get_sel_var(svar_offsetp+jp);
                            const auto& fanins2 = svar_map[svar_offsetp + jp];

                            if (lex_compare<int, FI>(fanins1, fanins2) == 1) {
                                pLits[1] = Abc_Var2Lit(sel_varp, 1);
                                auto status = 
                                    solver_add_clause(*solver, pLits, pLits+2);
                                assert(status);
                            }
                        }
                    }

                    svar_offset += nr_svars_for_i;
                }
            }

            /*******************************************************************
                Ensure that Boolean operators are lexicographically ordered:
                (S_ijk /\ S_(i+1)jk) ==> f_i <= f_(i+1)
            *******************************************************************/
            template<typename TT>
            void 
            create_lex_func_clauses(const synth_spec<TT>& spec)
            {
                std::bitset<FI> fvar_asgns;
                int lits[3];

                auto svar_offset = 0;
                for (int i = 0; i < spec.nr_steps - 1; i++) {
                    const auto nr_svars_for_i = nr_svar_map[i];
                    for (int j = 0; j < nr_svars_for_i; j++) {
                        const auto sel_var = get_sel_var(svar_offset + j);
                        const auto& fanins1 = svar_map[svar_offset + j];
                        Vec_IntSetEntry(vLits, 0, Abc_Var2Lit(sel_var, 1));
                        
                        auto svar_offsetp = svar_offset + nr_svars_for_i;
                        const auto nr_svars_for_ip = nr_svar_map[i + 1];
                        for (int jp = 0; jp < nr_svars_for_ip; jp++) {
                            const auto sel_varp = get_sel_var(svar_offsetp + jp);
                            const auto& fanins2 = svar_map[svar_offsetp + jp];

                            bool equal_fanin = true;
                            for (int k = 0; k < FI; k++) {
                                if (fanins1[k] != fanins2[k]) {
                                    equal_fanin = false;
                                    break;
                                }
                            }
                            if (!equal_fanin) {
                                continue;
                            }

                            Vec_IntSetEntry(vLits, 1, Abc_Var2Lit(sel_varp, 1));
                            
                            // The steps have the same fanin, so enforce lexicographical order.
                            // We do this by constraining the operator variables of both steps.
                            // Note: the operator variable with the highest index is used 
                            // first in the ordering.
                            for (int op_idx = 0; op_idx < nr_op_vars_per_step; op_idx++) {
                                // Inequality only has to hold if all previous operator variables
                                // are equal.
                                auto ctr = 2;
                                for (int prev_idx = 0; prev_idx < op_idx; prev_idx++) {
                                    const auto prev_alpha_i = get_lex_var(spec, i, prev_idx);
                                    Vec_IntSetEntry(vLits, ctr++, Abc_Var2Lit(prev_alpha_i, 1));
                                }

                                // Ensure that f_i_n <= f_{i+1}_n.
                                const auto iop_var = get_op_var(spec, i, nr_op_vars_per_step - op_idx);
                                const auto ipop_var = get_op_var(spec, i + 1, nr_op_vars_per_step - op_idx);
                                Vec_IntSetEntry(vLits, ctr++, Abc_Var2Lit(iop_var, 1));
                                Vec_IntSetEntry(vLits, ctr++, Abc_Var2Lit(ipop_var, 0));
                                auto status = solver_add_clause(*solver,
                                                                abc::Vec_IntArray(vLits),
                                                                abc::Vec_IntArray(vLits) + ctr);
                                assert(status);
                                if (op_idx == (nr_op_vars_per_step - 1)) {
                                    continue;
                                }
                                // alpha_i is 1 iff f_j_i == f_{j+1}_i.
                                auto alpha_i = get_lex_var(spec, i, op_idx);
                                lits[0] = Abc_Var2Lit(alpha_i, 1);
                                lits[1] = Abc_Var2Lit(iop_var, 0);
                                lits[2] = Abc_Var2Lit(ipop_var, 1);
                                solver_add_clause(*solver, lits, lits + 3);
                                lits[0] = Abc_Var2Lit(alpha_i, 1);
                                lits[1] = Abc_Var2Lit(iop_var, 1);
                                lits[2] = Abc_Var2Lit(ipop_var, 0);
                                solver_add_clause(*solver, lits, lits + 3);
                                lits[0] = Abc_Var2Lit(alpha_i, 0);
                                lits[1] = Abc_Var2Lit(iop_var, 1);
                                lits[2] = Abc_Var2Lit(ipop_var, 1);
                                solver_add_clause(*solver, lits, lits + 3);
                                lits[0] = Abc_Var2Lit(alpha_i, 0);
                                lits[1] = Abc_Var2Lit(iop_var, 0);
                                lits[2] = Abc_Var2Lit(ipop_var, 0);
                                solver_add_clause(*solver, lits, lits + 3);
                            }
                        }

                    }
                    svar_offset += nr_svars_for_i;
                }
            }

            /*******************************************************************
                Ensure that symmetric variables occur in order.
            *******************************************************************/
            template<typename TT>
            bool
            create_symvar_clauses(const synth_spec<TT>& spec)
            {
                for (int q = 1; q < spec.get_nr_in(); q++) {
                    for (int p = 0; p < q; p++) {
                        auto symm = true;
                        for (int i = 0; i < spec.nr_nontriv; i++) {
                            auto f = spec.functions[spec.synth_functions[i]];
                            if (!(swap(*f, p, q) == *f)) {
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

                        auto svar_offset = 0;
                        for (int i = 0; i < spec.nr_steps; i++) {
                            const auto nr_svars_for_i = nr_svar_map[i];
                            for (int j = 0; j < nr_svars_for_i; j++) {
                                const auto sel_var = get_sel_var(svar_offset+j);
                                const auto& fanins1 = svar_map[svar_offset+j];
                                
                                auto has_fanin_p = false;
                                auto has_fanin_q = false;
                                for (auto fanin : fanins1) {
                                    if (fanin == q) {
                                        has_fanin_q = true;
                                        break;
                                    } else if (fanin == p) {
                                        has_fanin_p = true;
                                    }
                                }
                                if (!has_fanin_q || has_fanin_p) {
                                    continue;
                                }

                                abc::Vec_IntSetEntry(vLits, 0, 
                                        Abc_Var2Lit(sel_var, 1));

                                auto ctr = 1;
                                auto svar_offsetp = 0;
                                for (int ip = 0; ip < i; ip++) {
                                    const auto nr_svars_for_ip = nr_svar_map[ip];
                                    for (int jp = 0; jp < nr_svars_for_ip; jp++) {
                                        const auto sel_varp = 
                                            get_sel_var(svar_offsetp + jp);
                                        const auto& fanins2 = 
                                            svar_map[svar_offsetp + jp];

                                        has_fanin_p = false;
                                        for (auto fanin : fanins2) {
                                            if (fanin == p) {
                                                has_fanin_p = true;
                                            }
                                        }
                                        if (!has_fanin_p) {
                                            continue;
                                        }
                                        abc::Vec_IntSetEntry(vLits, ctr++, 
                                                Abc_Var2Lit(sel_varp, 0));
                                    }
                                    svar_offsetp += nr_svars_for_ip;
                                }
                                if (!solver_add_clause(
                                            *solver, 
                                            Vec_IntArray(vLits), 
                                            Vec_IntArray(vLits) + ctr)) {
                                    return false;
                                }
                            }
                            svar_offset += nr_svars_for_i;
                        }
                    }
                }

                return true;
            }

            /*******************************************************************
                Ensure that every step has exactly 2 inputs. This may not
                happen e.g. when we synthesize with more than the minimum
                number of steps. (Example: synthesizing n-input OR function,
                with more than the minimum number of steps.)
            *******************************************************************/
            template<typename TT>
            void
            create_cardinality_constraints(const synth_spec<TT>& spec)
            {
                int pLits[2];

                auto svar_offset = 0;
                for (int i = 0; i < spec.nr_steps; i++) {
                    const auto nr_svars_for_i = nr_svar_map[i];
                    for (int j = 0; j < nr_svars_for_i - 1; j++) {
                        for (int jp = j + 1; jp < nr_svars_for_i; jp++) {
                            const auto svar1 = get_sel_var(svar_offset + j);
                            const auto svar2 = get_sel_var(svar_offset + jp);

                            pLits[0] = Abc_Var2Lit(svar1, 1);
                            pLits[1] = Abc_Var2Lit(svar2, 1);

                            auto status = solver_add_clause(
                                    *solver, 
                                    pLits, 
                                    pLits + 2);
                            assert(status);
                        }
                    }
                    svar_offset += nr_svars_for_i;
                }
                
                for (int h = 0; h < spec.nr_nontriv; h++) {
                    for (int i = 0; i < spec.nr_steps - 1; i++) {
                        for (int ip = i + 1; ip < spec.nr_steps; ip++) {
                            pLits[0] = Abc_Var2Lit(get_out_var(spec, h, i), 1);
                            pLits[1] = Abc_Var2Lit(get_out_var(spec, h, ip), 1);
                            auto status = solver_add_clause(
                                    *solver, 
                                    pLits, 
                                    pLits + 2);
                            assert(status);
                        }
                    }
                }
            }

            /// Extracts chain from encoded CNF solution.
            template<typename TT>
            void 
            extract_chain(synth_spec<TT>& spec, chain<FI>& chain)
            {
                chain.reset(spec.get_nr_in(), spec.get_nr_out(), spec.nr_steps);

                auto svar_offset = 0;
                for (int i = 0; i < spec.nr_steps; i++) {
                    kitty::static_truth_table<FI> op;
                    for (int j = 1; j <= nr_op_vars_per_step; j++) {
                        if (solver_var_value(*solver, get_op_var(spec, i, j))) {
                            kitty::set_bit(op, j); 
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
                        if (solver_var_value(*solver, sel_var)) {
                            const auto& fanins = svar_map[svar_offset + j];
                            if (spec.verbosity) {
                                printf("  with operands ");
                                for (int k = 0; k < FI; k++) {
                                    printf("x_%d ", fanins[k] + 1);
                                }
                            }
                            chain.set_step(i, fanins, op);
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
                        if (solver_var_value(*solver, 
                                    get_out_var(spec, nontriv_count, i))) {
                            chain.set_output(h, 
                                    ((i + spec.get_nr_in() + 1) << 1) +
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
                            if (solver_var_value(*solver,
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

                printf("  Nr. variables = %d\n", solver_nr_vars(*solver));
                printf("  Nr. clauses = %d\n\n", solver_nr_clauses(*solver));

                auto svar_offset = 0;
                for (int i = 0; i < spec.nr_steps; i++) {
                    bool step_has_fanins = false;
                    const auto nr_svars_for_i = nr_svar_map[i];
                    for (int j = 0; j < nr_svars_for_i; j++) {
                        const auto sel_var = get_sel_var(svar_offset + j);
                        if (solver_var_value(*solver, sel_var)) {
                            const auto& fanins = svar_map[svar_offset + j];
                            printf("  x_%d has inputs ", 
                                    spec.get_nr_in() + i + 1);
                            for (int k = FI-1; k >= 0; k--) {
                                printf("x_%d ", fanins[k] + 1);
                            }
                            step_has_fanins = true;
                        }
                    }
                    svar_offset += nr_svars_for_i;
                    if (!step_has_fanins) {
                        printf("  no fanins found for x_%d\n",
                                spec.get_nr_in() + i + 1);
                    }

                    printf("  f_%d = ", spec.get_nr_in()+i+1);
                    for (int oidx = nr_op_vars_per_step; oidx > 0; oidx--) {
                        printf("%d", solver_var_value(*solver, 
                                    get_op_var(spec, i, oidx)));
                    }
                    printf("0\n");

                    printf("  tt_%d = ", spec.get_nr_in() + i + 1);
                    for (int t = spec.get_tt_size() - 1; t >= 0; t--) {
                        printf("%d", solver_var_value(*solver, 
                                    get_sim_var(spec, i, t)));
                    }
                    printf("0\n\n");
                }

                for (int h = 0; h < spec.nr_nontriv; h++) {
                    for (int i = 0; i < spec.nr_steps; i++) {
                        printf("  g_%d_%d=%d\n", h + 1, 
                                spec.get_nr_in() + i + 1,
                                solver_var_value(
                                    *solver, get_out_var(spec, h, i)));
                    }
                }
                printf("\n");

                svar_offset = 0;
                for (int i = 0; i < spec.nr_steps; i++) {
                    const auto nr_svars_for_i = nr_svar_map[i];
                    for (int j = 0; j < nr_svars_for_i; j++) {
                        printf("  s_%d", spec.get_nr_in() + i + 1);
                        const auto& fanins = svar_map[j + svar_offset];
                        for (auto fi : fanins) {
                            printf("_%d", fi + 1);
                        }
                        printf("=%d\n", solver_var_value(*solver,
                                    get_sel_var(j + svar_offset)));
                    }
                    printf("\n");

                    for (int oidx = nr_op_vars_per_step; oidx > 0; oidx--) {
                        printf("  f_%d_%d=%d\n", 
                                spec.get_nr_in() + i + 1, 
                                oidx + 1,
                                solver_var_value(
                                    *solver, get_op_var(spec, i, oidx))
                              );
                    }
                    printf("  f_%d_1=0\n", spec.get_nr_in() + i + 1);
                    printf("\n");

                    for (int t = spec.get_tt_size() - 1; t >= 0; t--) {
                        printf("  x_%d_%d=%d\n", spec.get_nr_in() + i+1, t + 2, 
                                solver_var_value(*solver, 
                                    get_sim_var(spec, i, t)));
                    }
                    printf("  x_%d_0=0\n", spec.get_nr_in() + i + 1);
                    printf("\n");

                    svar_offset += nr_svars_for_i;
                }
                printf("\n");

                printf("========================================"
                        "========================================\n");
            }

			/// Encodes specifciation for use in standard synthesis flow.
            template<typename TT>
            bool 
            encode(const synth_spec<TT>& spec)
            {
                assert(spec.nr_steps <= MAX_STEPS);

                create_variables(spec);
                if (!create_main_clauses(spec)) {
                    return false;
                }

                if (!create_output_clauses(spec)) {
                    return false;
                }

                if (!create_op_clauses(spec)) {
                    return false;
                }
                
                create_cardinality_constraints(spec);

                if (spec.add_nontriv_clauses) {
                    create_nontriv_clauses(spec);
                }

                if (spec.add_alonce_clauses) {
                    create_alonce_clauses(spec);
                }

                if (spec.add_noreapply_clauses) {
                    create_noreapply_clauses(spec);
                }

                if (spec.add_colex_clauses) {
                    create_colex_clauses(spec);
                }

                if (spec.add_lex_clauses) {
                    create_lex_clauses(spec);
                }
                
                if (spec.add_lex_func_clauses) {
                    create_lex_func_clauses(spec);
                }
                
                if (spec.add_symvar_clauses && !create_symvar_clauses(spec)) {
                    return false;
                }

                return true;
            }

			/// Encodes specifciation for use in CEGAR based synthesis flow.
            template<typename TT>
            bool 
            cegar_encode(const synth_spec<TT>& spec)
            {
                assert(spec.nr_steps <= MAX_STEPS);

                create_variables(spec);
                for (int i = 0; i < spec.nr_rand_tt_assigns; i++) {
                    if (!create_tt_clauses(spec, rand() % spec.get_tt_size())) {
                        return false;
                    }
                }
                
                if (!create_output_clauses(spec)) {
                    return false;
                }
                
                if (!create_op_clauses(spec)) {
                    return false;
                }
                
                create_cardinality_constraints(spec);

                if (spec.add_nontriv_clauses) {
                    create_nontriv_clauses(spec);
                }

                if (spec.add_alonce_clauses) {
                    create_alonce_clauses(spec);
                }
                
                if (spec.add_noreapply_clauses) {
                    create_noreapply_clauses(spec);
                }
                
                if (spec.add_colex_clauses) {
                    create_colex_clauses(spec);
                }
                
                if (spec.add_lex_clauses) {
                    create_lex_clauses(spec);
                }

                if (spec.add_lex_func_clauses) {
                    create_lex_func_clauses(spec);
                }

                if (spec.add_symvar_clauses && !create_symvar_clauses(spec)) {
                    return false;
                }

                return true;
            }

            /// Assumes that a solution has been found by the current encoding.
            /// Blocks the current solution such that the solver is forced to
            /// find different ones (if they exist).
            template<typename TT>
            bool
            block_solution(const synth_spec<TT>& spec)
            {
                int ctr = 0;
                int svar_offset = 0;

                for (int i = 0; i < spec.nr_steps; i++) {
                    for (int j = 1; j <= nr_op_vars_per_step; j++) {
                        int invert = 0;
                        const auto op_var = get_op_var(spec, i, j);
                        if (solver_var_value(*solver, op_var)) {
                            invert = 1;
                        }
                        abc::Vec_IntSetEntry(vLits, ctr++,
                                abc::Abc_Var2Lit(get_op_var(spec, i, j),
                                    invert));
                    }

                    const auto nr_svars_for_i = nr_svar_map[i];
                    for (int j = 0; j < nr_svars_for_i; j++) {
                        const auto sel_var = get_sel_var(svar_offset + j);
                        if (solver_var_value(*solver, sel_var)) {
                            abc::Vec_IntSetEntry(vLits, ctr++,
                                    abc::Abc_Var2Lit(sel_var, 1));
                            break;
                        }
                    }

                    svar_offset += nr_svars_for_i;
                }
                
                return solver_add_clause(
                            *solver,
                            abc::Vec_IntArray(vLits), 
                            abc::Vec_IntArray(vLits) + ctr);
            }


            /// Similar to block_solution, but blocks all solutions with the
            /// same structure. This is more restrictive, since the other
            /// method allows for the same structure but different operators.
            template<typename TT>
            bool
            block_struct_solution(const synth_spec<TT>& spec)
            {
                int ctr = 0;
                int svar_offset = 0;

                for (int i = 0; i < spec.nr_steps; i++) {
                    const auto nr_svars_for_i = nr_svar_map[i];
                    for (int j = 0; j < nr_svars_for_i; j++) {
                        const auto sel_var = get_sel_var(svar_offset + j);
                        if (solver_var_value(*solver, sel_var)) {
                            abc::Vec_IntSetEntry(vLits, ctr++,
                                    abc::Abc_Var2Lit(sel_var, 1));
                            break;
                        }
                    }

                    svar_offset += nr_svars_for_i;
                }

                return solver_add_clause(
                            *solver,
                            abc::Vec_IntArray(vLits), 
                            abc::Vec_IntArray(vLits) + ctr);
            }
    };
}

