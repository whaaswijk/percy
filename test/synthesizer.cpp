#include <percy/percy.hpp>
#include <cassert>
#include <cstdio>
#include <fstream>

using namespace percy;
using kitty::dynamic_truth_table;

/*******************************************************************************
    Tests the exact synthesis functionality of the package.
*******************************************************************************/
int main(void)
{
    
    spec spec;
    spec.verbosity = 0;

    chain c;

    dynamic_truth_table tti(2);
    dynamic_truth_table ttj(2);

    for (int i = 0; i < 16; i++) {
        kitty::create_from_words(tti, &i, &i + 1);
        spec[0] = tti;
        auto result = synthesize(spec, c);
        assert(result == success);
        c.satisfies_spec(spec);
    }

    spec.set_nr_out(2);
    for (int i = 0; i < 16; i++) {
        kitty::create_from_words(tti, &i, &i + 1);
        spec[0] = tti;
        for (int j = 0; j < 16; j++) {
            kitty::create_from_words(ttj, &j, &j + 1);
            spec[1] = ttj;
            auto result = synthesize(spec, c);
            assert(result == success);
            assert(c.get_nr_steps() <= 2);
            c.satisfies_spec(spec);
        }
    }
    
    // Synthesize a full adder
    // Create the truth table specification object. It has three inputs and two outputs.
    spec.fanin = 3;
    spec.verbosity = 0;

    // Create the functions to synthesize.
    // We use three static truth tables to 
    // represent the three inputs to the full adder.
    dynamic_truth_table x(3), y(3), z(3);

    create_nth_var(x, 0);
    create_nth_var(y, 1);
    create_nth_var(z, 2);

    // The sum and carry functions represent the outputs of the 
    // chain that we want to synthesize. 
    const auto sum = x ^ y ^ z;
    const auto carry = ternary_majority(x, y, z);
    spec[0] = sum;
    spec[1] = carry;

    // Call the synthesizer with the specification we've constructed.
    auto result = synthesize(spec, c);

    // Ensure that synthesis was successful.
    assert(result == success);

    // Simulate the synthesized circuit and ensure that it
    // computes the correct functions.
    auto sim_fs = c.simulate();
    assert(sim_fs[0] == sum);
    assert(sim_fs[1] == carry);

    return 0;
}

