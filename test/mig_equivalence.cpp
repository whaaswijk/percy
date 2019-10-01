#include <cstdio>
#include <percy/percy.hpp>
#include <chrono>

#define MAX_TESTS 256

using namespace percy;
using kitty::dynamic_truth_table;


int main()
{
    {
        // Synthesize 4-input function with mig 
        mig mig;
        spec spec;
        spec.verbosity = 1; 
        bsat_wrapper solver;
        mig_encoder encoder(solver);
        kitty::dynamic_truth_table tt(4);
        kitty::create_from_hex_string(tt, "19e6");
        spec[0] = tt;
         
        auto res = mig_synthesize(spec, mig, solver, encoder);
        const auto sim_tts = mig.simulate();

        assert (sim_tts[0] == tt);
        assert (mig.get_nr_steps() == 5);
        assert (mig.get_nr_inputs() == 4);
        assert (mig.satisfies_spec( spec ) == true);
    }
    {
        // // Synthesize 4-input function with mig enumerate solutions
        mig mig;
        spec spec;
        spec.verbosity = 1; 
        bsat_wrapper solver;
        mig_encoder encoder(solver);
        kitty::dynamic_truth_table tt(4);
        kitty::create_from_hex_string(tt, "01ef");
        spec[0] = tt;

        auto res = mig_synthesize(spec, mig, solver, encoder);
        const auto sim_tts = mig.simulate();

        assert (sim_tts[0] == tt);
        assert (mig.get_nr_steps() == 4);
        assert (mig.get_nr_inputs() == 4);
        assert (mig.satisfies_spec( spec ) == true);
    }

    return 0;
}

