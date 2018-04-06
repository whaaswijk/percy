#pragma once

#include <kitty/kitty.hpp>
#include "../spec.hpp"
#include "../encoders.hpp"

using kitty::dynamic_truth_table;

namespace percy
{
    /***************************************************************************
        This enum keeps track of the different available synthesizers.
    ***************************************************************************/
    enum synth_type
    {
        STD,
        FENCE,
        DAG,
    };
    
    template<typename Encoder, typename Solver>
    class synthesizer
    {
        protected:
            Solver solver;
            Encoder encoder;

        public:
            synthesizer()
            {
                solver_alloc(&solver);
                encoder.set_solver(&solver);
            }
            
            ~synthesizer()
            {
                solver_dealloc(&solver);
            }
    };
    
}
 
