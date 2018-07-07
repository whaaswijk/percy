#include <cstdio>
#include <percy/percy.hpp>

using namespace percy;

/// Test the generation of CNF output from encoded exact synthesis instances.
int
main(void)
{
    spec spec;

    kitty::dynamic_truth_table tt(4);
    kitty::create_from_hex_string(tt, "cafe");

    spec[0] = tt;
    chain c;

    // Synthesize it to see what the minimum number of steps is.
    auto status = synthesize(spec, c);
    assert(status == success);
    const auto min_nr_steps = c.get_nr_steps();
    
    // Generate cnf formulas up to the minimum nr of steps and
    // make sure that all but the last are UNSAT.
    cnf_formula cnf;
    knuth_encoder encoder(cnf);

    for (int i = 1; i <= min_nr_steps; i++) {
        const auto filename = std::string("cnf_") + std::to_string(i) + std::string(".cnf");

        auto fhandle = fopen(filename.c_str(), "w");
        if (fhandle == NULL) {
            fprintf(stderr, "Error: unable to open CNF output file\n");
            return 1;
        }
        spec.nr_steps = i;
        spec.preprocess();

        cnf.clear();
        encoder.encode(spec);
        cnf.to_cnf(fhandle);
        fclose(fhandle);
    }

    return 0;
}

