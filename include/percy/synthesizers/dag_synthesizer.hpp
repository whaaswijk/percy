#pragma once

#include "synthesizer_base.hpp"

namespace percy
{
    template<
        int FI=2, 
        typename Encoder=dag_encoder<dag<FI>>, 
        typename Solver=sat_solver*>
    class dag_synthesizer :
        public synthesizer<Encoder, Solver>
    {
        using synthesizer<Encoder, Solver>::solver;
        using synthesizer<Encoder, Solver>::encoder;

        public:
            template<typename TT>
            synth_result 
            synthesize(
                    synth_spec<TT>& spec, 
                    const dag<FI>& dag, 
                    chain<FI>& chain,
                    bool preprocess_spec=true)
            {
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
}

