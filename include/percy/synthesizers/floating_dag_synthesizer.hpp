#pragma once

#include "synthesizer.hpp"

namespace percy
{
    template<int FI=2>
    class floating_dag_synthesizer
    {
        std::unique_ptr<solver_wrapper> solver;
        std::unique_ptr<floating_dag_encoder> encoder;

        public:
            floating_dag_synthesizer(std::unique_ptr<solver_wrapper> solver)
            {
                this->solver = std::move(solver);
                encoder->set_solver(this->solver.get());
            }

            template<int FI>
            synth_result 
            synthesize(
                    const spec& spec, 
                    const floating_dag<FI>& dag, 
                    chain& chain,
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

