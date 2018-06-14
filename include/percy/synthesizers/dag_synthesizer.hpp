#pragma once

#include "synthesizer.hpp"

namespace percy
{
    /*
    class dag_synthesizer
    {
    protected:
        std::unique_ptr<solver_wrapper> solver;
        std::unique_ptr<dag_encoder> encoder;

    public:
        template<int FI>
        synth_result
        synthesize(spec& spec, const dag<FI>& dag, chain& chain, bool preprocess_spec = true)
        {
            assert(spec.fanin == chain.get_fanin());
            assert(chain.get_fanin() == FI);

            if (preprocess_spec) {
                spec.preprocess();
            }

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

            solver_restart(&solver);
            if (!encoder.encode(spec, dag)) {
                return failure;
            }

            auto status = solver_solve(solver, spec.conflict_limit);
            if (status == success) {
                encoder.extract_chain(spec, dag, chain);
            }

            return status;
        }
    };
    */
}

