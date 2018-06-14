#pragma once

#include <kitty/kitty.hpp>
#include <memory>
#include "../spec.hpp"
#include "../encoders.hpp"
#include "../solvers.hpp"

namespace percy
{
    /// The synthesizer base class. All synthesizers have some Encoder and
    /// some Solver, which they compose to perform synthesis.
    /*
    class synthesizer
    {
        protected:
            std::unique_ptr<solver_wrapper> solver;
            std::unique_ptr<encoder> encoder;

        public:
            synthesizer()
            {
                encoder->set_solver(solver.get());
            }
    };
    */
    
}
 
