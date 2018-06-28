#include <percy/percy.hpp>
#include <kitty/kitty.hpp>
#include <cassert>
#include <cstdio>
#include <fstream>

using namespace percy;
using kitty::dynamic_truth_table;

/// Tests synthesis using a restricted set of logic primitives.
int main(void)
{
    chain c;
    spec spec;
    spec.verbosity = 0;

    bsat_wrapper solver;
    knuth_encoder encoder(solver);


    // Synthesize a majority 5 with majority 3s
    dynamic_truth_table maj5(5);
    kitty::create_majority(maj5);
    spec.fanin = 3;
    spec.add_primitive(MAJ);
    spec.compile_primitives();
    spec[0] = maj5;

    printf("synthesizing %s\n", kitty::to_binary(maj5).c_str());
    auto result = synthesize(spec, c, solver, encoder);
    assert(result == success);
    auto tts = c.simulate(spec);
    assert(tts[0] == maj5);
    assert(c.get_nr_steps() == 4);

    dynamic_truth_table maj7(7);
    kitty::create_majority(maj7);
    spec[0] = maj7;
    printf("synthesizing %s\n", kitty::to_binary(maj7).c_str());
    result = synthesize(spec, c, solver, encoder);
    assert(result == success);
    tts = c.simulate(spec);
    assert(tts[0] == maj7);
    assert(c.get_nr_steps() == 7);

    return 0;
}

