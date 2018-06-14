#pragma once

#include "synthesizer.hpp"

namespace percy
{
    /*
    /// Standard synthesizer class that uses conventional SAT based synthesis
    /// techniques.
    class std_synthesizer : public synthesizer
    {
    private:
        bool is_dirty = false;

    public:
        std_synthesizer(std::unique_ptr<solver_wrapper> solver)
        {
            this->solver = std::move(solver);
            encoder->set_solver(this->solver.get());
        }

        /*
        /// Performs exact synthesis using a standard synthesis loop.
        /// Given the specifcation \p spec it stores the result of
        /// synthesis in \p chain. Using \p initial_steps we can give a
        /// specify the initial number of steps to start synthesis from.
        /// Note that this may lead to suboptimal results.
        synth_result
        synthesize(spec& spec, chain& chain, const int initial_steps = 1)
        {
            assert(spec.get_nr_in() >= spec.fanin);

            is_dirty = true;

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

            spec.nr_steps = initial_steps;
            while (true) {
                solver->restart();
                if (!encoder->encode(spec)) {
                    spec.nr_steps++;
                    continue;
                }

                auto begin = std::chrono::steady_clock::now();
                const auto status = solver->solve(spec.conflict_limit);
                auto end = std::chrono::steady_clock::now();
                auto synth_time =
                    std::chrono::duration_cast<std::chrono::microseconds>(
                        end - begin
                        ).count();
                spec.synth_time = synth_time;

                if (status == success) {
                    encoder->extract_chain(spec, chain);
                    if (spec.verbosity > 2) {
                        //    encoder.print_solver_state(spec);
                    }
                    return success;
                } else if (status == failure) {
                    spec.nr_steps++;
                } else {
                    return timeout;
                }
            }
        }

        /// Performs synthesis using a CEGAR loop.
        synth_result
        cegar_synthesize(spec& spec, chain& chain, const int initial_steps = 1)
        {
            assert(spec.get_nr_in() >= spec.fanin);

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

            is_dirty = true;
            spec.nr_rand_tt_assigns = 2 * spec.get_nr_in();
            spec.nr_steps = initial_steps;
            while (true) {
                solver->restart();
                if (!encoder->cegar_encode(spec)) {
                    spec.nr_steps++;
                    continue;
                }
                while (true) {
                    auto stat = solver->solve(spec.conflict_limit);
                    if (stat == success) {
                        encoder->extract_chain(spec, chain);
                        auto sim_tts = chain_simulate(chain, spec);
                        auto xor_tt = (sim_tts[0]) ^ (spec.functions[0]);
                        auto first_one = kitty::find_first_one_bit(xor_tt);
                        if (first_one == -1) {
                            return success;
                        }
                        // Add additional constraint.
                        if (spec.verbosity) {
                            printf("  CEGAR difference at tt index %ld\n",
                                first_one);
                        }
                        if (!encoder->create_tt_clauses(spec, first_one - 1)) {
                            spec.nr_steps++;
                            break;
                        }
                    } else if (stat == failure) {
                        spec.nr_steps++;
                        break;
                    } else {
                        return timeout;
                    }
                }
            }
        }

        /// Generates the next solution. This can be used in a loop to enumerate
        /// different solutions to a specification.
        synth_result
        next_solution(spec& spec, chain& chain, const int initial_steps = 1)
        {
            if (!is_dirty) {
                return synthesize(spec, chain, initial_steps);
            }

            // The special case when the Boolean chain to be synthesized
            // consists entirely of trivial functions.
            // In this case, only one solution exists.
            if (spec.nr_triv == spec.get_nr_out()) {
                return failure;
            }


            while (encoder->block_solution(spec)) {
                const auto status = solver->solve(spec.conflict_limit);

                if (status == success) {
                    encoder->extract_chain(spec, chain);
                    return success;
                } else {
                    return status;
                }
            }

            return failure;
        }

        /// Generates the next *structurally different* solution, where structure
        /// refers to the underlying DAG structure of a solution. This method can 
        /// be used in a loop to enumerate structurally different solutions to a 
        /// specification.
        synth_result next_struct_solution(spec& spec, chain& chain)
        {
            if (!is_dirty) {
                auto result = synthesize(spec, chain);
                // assert(result == success);
                return result;
            }

            // The special case when the Boolean chain to be synthesized
            // consists entirely of trivial functions.
            // In this case, only one solution exists.
            if (spec.nr_triv == spec.get_nr_out()) {
                return failure;
            }

            while (encoder->block_struct_solution(spec)) {
                const auto status = solver->solve(spec.conflict_limit);

                if (status == success) {
                    encoder->extract_chain(spec, chain);
                    return success;
                } else {
                    return status;
                }
            }

            return failure;
        }

        /// Resets synthesizer state. Used in generating multiple solutions.
        void reset()
        {
            is_dirty = false;
        }

    };
        */
}

