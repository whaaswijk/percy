#pragma once

#include "synthesizer_base.hpp"

namespace percy
{
    /***************************************************************************
        Standard synthesizer class that uses conventional SAT based synthesis
        techniques.
    ***************************************************************************/
    template<
        int FI=2, 
        typename Encoder=knuth_encoder<FI>, 
        typename Solver=sat_solver*>
    class std_synthesizer : public synthesizer<Encoder, Solver>
    {
        using synthesizer<Encoder, Solver>::solver;
        using synthesizer<Encoder, Solver>::encoder;

        public:
            template<typename TT>
            synth_result 
            synthesize(synth_spec<TT>& spec, chain<FI>& chain)
            {
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

                spec.nr_steps = 1;
                while (true) {
                    solver_restart(&solver);
                    if (!encoder.encode(spec)) {
                        spec.nr_steps++;
                        continue;
                    }
                    const auto status = 
                        solver_solve(solver, spec.conflict_limit);

                    if (status == success) {
                        encoder.extract_chain(spec, chain);
                        if (spec.verbosity > 2) {
                            encoder.print_solver_state(spec);
                        }
                        return success;
                    } else if (status == failure) {
                        spec.nr_steps++;
                    } else {
                        return timeout;
                    }
                }
            }
            
            template<typename TT>
            synth_result
            cegar_synthesize(synth_spec<TT>& spec, chain<FI>& chain)
            {
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
                spec.nr_steps = 1;
                solver_restart(&solver);
                while (true) {
                    if (!encoder.cegar_encode(spec)) {
                        spec.nr_steps++;
                        continue;
                    }
                    auto status = solver_solve(solver, spec.conflict_limit);
                    if (status == success) {
                        encoder.extract_chain(spec, chain);
                        auto sim_tts = chain.template simulate<TT>();
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
                            spec.nr_steps++;
                            solver_restart(&solver);
                        }
                    } else if (status == failure) {
                        spec.nr_steps++;
                        solver_restart(&solver);
                    } else {
                        return timeout;
                    }
                }
            }

    };
}

