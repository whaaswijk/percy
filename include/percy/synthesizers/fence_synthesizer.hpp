#pragma once

#include "synthesizer_base.hpp"

namespace percy
{
    /***************************************************************************
        Extends the colex_func_synthesizer and adds clauses that constrain the 
        synthesized Boolbean chain to specific graph topologies.
    ***************************************************************************/
    template<
        int FI=2, 
        typename Encoder=fence_encoder<FI>,
        typename Solver=sat_solver*>
    class fence_synthesizer : 
        public synthesizer<Encoder, Solver>
    {
        using synthesizer<Encoder, Solver>::solver;
        using synthesizer<Encoder, Solver>::encoder;

        public:
            template<typename TT>
            synth_result 
            synthesize(
                    synth_spec<TT>& spec, 
                    chain<FI>& chain,
                    const int initial_steps = 1)
            {
                assert(spec.get_nr_in() >= FI);

                spec.preprocess();

                // The special case when the Boolean chain to be synthesized
                // consists entirely of trivial functions.
                if (spec.nr_triv == spec.get_nr_out()) {
                    chain.reset(spec.get_nr_in(), spec.get_nr_out(), 0);
                    for (int h = 0; h < spec.get_nr_out(); h++) {
                        chain.set_output(h, (spec.triv_functions[h] << 1) +
                                ((spec.out_inv >> h) & 1));
                    }
                    return success;
                }

                // As the topological synthesizer decomposes the synthesis
                // problem, to fairly count the total number of conflicts we
                // should keep track of all conflicts in existence checks.
                int total_conflicts = 0;
                fence f;
                po_filter<unbounded_generator> g(
                        unbounded_generator(initial_steps), 
                        spec.get_nr_out(), FI);
                int old_nnodes = 1;
                while (true) {
                    g.next_fence(f);
                    spec.nr_steps = f.nr_nodes();

                    if (spec.nr_steps > old_nnodes) {
                        // Reset conflict count, since this is where other
                        // synthesizers reset it.
                        total_conflicts = 0;
                        old_nnodes = spec.nr_steps;
                    }

                    solver_restart(&solver);
                    if (!encoder.encode(spec, f)) {
                        continue;
                    }

                    if (spec.verbosity) {
                        printf("  next fence:\n");
                        print_fence(f);
                        printf("\n");
                        printf("nr_nodes=%d, nr_levels=%d\n", f.nr_nodes(), 
                                f.nr_levels());
                        for (int i = 0; i < f.nr_levels(); i++) {
                            printf("f[%d] = %d\n", i, f[i]);
                        }
                    }
                    auto status = solver_solve(solver, spec.conflict_limit);
                    if (status == success) {
                        encoder.extract_chain(spec, chain);
                        return success;
                    } else if (status == failure) {
                        total_conflicts += solver_nr_conflicts(solver);
                        if (spec.conflict_limit &&
                                total_conflicts > spec.conflict_limit) {
                            return timeout;
                        }
                        continue;
                    } else {
                        return timeout;
                    }
                }
            }

            template<typename TT>
            synth_result 
            synthesize(synth_spec<TT>& spec, const fence& f, chain<FI>& chain)
            {
                assert(spec.get_nr_in() >= FI);

                spec.preprocess();

                // The special case when the Boolean chain to be synthesized
                // consists entirely of trivial functions.
                if (spec.nr_triv == spec.get_nr_out()) {
                    chain.reset(spec.get_nr_in(), spec.get_nr_out(), 0);
                    for (int h = 0; h < spec.get_nr_out(); h++) {
                        chain.set_output(h, (spec.triv_functions[h] << 1) +
                                ((spec.out_inv >> h) & 1));
                    }
                    return success;
                }
                
                spec.nr_steps = f.nr_nodes();

                solver_restart(&solver);
                if (!encoder.encode(spec, f)) {
                    return failure;
                }

                if (spec.verbosity) {
                    printf("  fence:\n");
                    print_fence(f);
                    printf("\n");
                    printf("nr_nodes=%d, nr_levels=%d\n", f.nr_nodes(), 
                            f.nr_levels());
                    for (int i = 0; i < f.nr_levels(); i++) {
                        printf("f[%d] = %d\n", i, f.at(i));
                    }
                }

                auto status = solver_solve(solver, spec.conflict_limit);
                if (status == success) {
                    encoder.extract_chain(spec, chain);
                    return success;
                } else if (status == failure) {
                    return failure;
                } else {
                    return timeout;
                }
            }

            template<typename TT>
            synth_result
            cegar_synthesize(
                    synth_spec<TT>& spec, 
                    chain<FI>& chain,
                    const int initial_steps = 1)
            {
                assert(spec.get_nr_in() >= FI);

                spec.preprocess();

                // The special case when the Boolean chain to be synthesized
                // consists entirely of trivial functions.
                if (spec.nr_triv == spec.get_nr_out()) {
                    chain.reset(spec.get_nr_in(), spec.get_nr_out(), 0);
                    for (int h = 0; h < spec.get_nr_out(); h++) {
                        chain.set_output(h, (spec.triv_functions[h] << 1) +
                                ((spec.out_inv >> h) & 1));
                    }
                    return success;
                }

                spec.nr_rand_tt_assigns = 2 * spec.get_nr_in();

                fence f;
                po_filter<unbounded_generator> g(
                        unbounded_generator(initial_steps), 
                        spec.get_nr_out(), FI);
                int total_conflicts = 0;
                int old_nnodes = 1;
                while (true) {
                    g.next_fence(f);
                    spec.nr_steps = f.nr_nodes();

                    if (spec.nr_steps > old_nnodes) {
                        // Reset conflict count, since this is where other
                        // synthesizers reset it.
                        total_conflicts = 0;
                        old_nnodes = spec.nr_steps;
                    }

                    if (spec.verbosity) {
                        printf("  next fence:\n");
                        print_fence(f);
                        printf("\n");
                        printf("nr_nodes=%d, nr_levels=%d\n", f.nr_nodes(), 
                                f.nr_levels());
                        for (int i = 0; i < f.nr_levels(); i++) {
                            printf("f[%d] = %d\n", i, f[i]);
                        }
                    }

                    solver_restart(&solver);
                    if (!encoder.cegar_encode(spec, f)) {
                        continue;
                    }
                    while (true) {
                        auto status = solver_solve(solver, spec.conflict_limit);
                        if (status == success) {
                            encoder.extract_chain(spec, chain);
                            auto sim_tts = chain_simulate(chain, spec);
                            auto xor_tt = (sim_tts[0]) ^ (*spec.functions[0]);
                            auto first_one = kitty::find_first_one_bit(xor_tt);
                            if (first_one == -1) {
                                if (spec.verbosity) {
                                    printf("  SUCCESS\n\n"); 
                                }
                                return success;
                            }
                            // Add additional constraint.
                            if (spec.verbosity) {
                                printf("  CEGAR difference at tt index %ld\n", 
                                        first_one);
                            }
                            if (!encoder.create_tt_clauses(spec, first_one-1)) {
                                break;
                            }
                        } else if (status == failure) {
                            break;
                        } else {
                            return timeout;
                        }
                    }
                }
            }

            template<typename TT>
            synth_result
            cegar_synthesize(
                    synth_spec<TT>& spec, 
                    const fence& f, 
                    chain<FI>& chain)
            {
                assert(spec.get_nr_in() >= FI);

                spec.preprocess();

                // The special case when the Boolean chain to be synthesized
                // consists entirely of trivial functions.
                if (spec.nr_triv == spec.get_nr_out()) {
                    chain.reset(spec.get_nr_in(), spec.get_nr_out(), 0);
                    for (int h = 0; h < spec.get_nr_out(); h++) {
                        chain.set_output(h, (spec.triv_functions[h] << 1) +
                                ((spec.out_inv >> h) & 1));
                    }
                    return success;
                }

                spec.nr_rand_tt_assigns = 2 * spec.get_nr_in();
                spec.nr_steps = f.nr_nodes();
                if (spec.verbosity) {
                    printf("  fence:\n");
                    print_fence(f);
                    printf("\n");
                    printf("nr_nodes=%d, nr_levels=%d\n", f.nr_nodes(), 
                            f.nr_levels());
                    for (int i = 0; i < f.nr_levels(); i++) {
                        printf("f[%d] = %d\n", i, f.at(i));
                    }
                }

                solver_restart(&solver);
                if (!encoder.cegar_encode(spec, f)) {
                    return failure;
                }
                while (true) {
                    auto status = solver_solve(solver, spec.conflict_limit);
                    if (status == success) {
                        encoder.extract_chain(spec, chain);
                        auto sim_tts = chain_simulate(chain, spec);
                        auto xor_tt = (sim_tts[0]) ^ (*spec.functions[0]);
                        auto first_one = kitty::find_first_one_bit(xor_tt);
                        if (first_one == -1) {
                            if (spec.verbosity) {
                                printf("  SUCCESS\n\n"); 
                            }
                            return success;
                        }
                        // Add additional constraint.
                        if (spec.verbosity) {
                            printf("  CEGAR difference at tt index %ld\n", 
                                    first_one);
                        }
                        if (!encoder.create_tt_clauses(spec, first_one-1)) {
                            break;
                        }
                    } else if (status == failure) {
                        break;
                    } else {
                        return timeout;
                    }
                }
            }
    };

}

