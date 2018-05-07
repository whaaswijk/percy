#include <cstdio>
#include <percy/percy.hpp>
#include <kitty/kitty.hpp>

#define MAX_TESTS 256

using namespace percy;
using kitty::static_truth_table;

/*******************************************************************************
    Verifies that our synthesizers' results are equivalent to each other.
*******************************************************************************/
template<int NrIn>
void check_std_equivalence(bool full_coverage)
{
    synth_spec<static_truth_table<NrIn>> spec(NrIn, 1);

    auto synth1 = new_std_synth();
    auto synth2 = new_std_synth<2, Glucose::MultiSolvers*>();

    spec.verbosity = 0;

    chain<2> c1, c1_cegar, c2, c2_cegar;

    // Don't run too many tests.
    auto max_tests = (1 << (1 << NrIn));
    if (!full_coverage) {
        max_tests = std::min(max_tests, MAX_TESTS);
    }
    static_truth_table<NrIn> tt;
    for (auto i = 1; i < max_tests; i++) {
        kitty::create_from_words(tt, &i, &i+1);

        spec.functions[0] = &tt;
        auto res1 = synth1->synthesize(spec, c1);
        assert(res1 == success);
        auto sim_tts1 = c1.template simulate(spec);
        auto c1_nr_steps = c1.get_nr_vertices();

        auto res1_cegar = synth1->cegar_synthesize(spec, c1_cegar);
        assert(res1_cegar == success);
        auto sim_tts1_cegar = c1_cegar.template simulate(spec);
        auto c1_cegar_nr_steps = c1_cegar.get_nr_vertices();

        auto res2 = synth2->synthesize(spec, c2);
        assert(res2 == success);
        auto sim_tts2 = c2.template simulate(spec);
        auto c2_nr_steps = c2.get_nr_vertices();

        /*
         * TODO: enable Glucose::MultiSolvers synthesis using CEGAR
        auto res2_cegar = synth2->cegar_synthesize(spec, c2_cegar);
        assert(res2_cegar == success);
        auto sim_tts2_cegar = c2_cegar.template simulate(spec);
        auto c2_cegar_nr_steps = c2_cegar.get_nr_vertices();
        */

        assert(c1_nr_steps == c2_nr_steps);
        assert(c1_nr_steps == c1_cegar_nr_steps);
        //assert(c1_cegar_nr_steps == c2_cegar_nr_steps);
        assert(sim_tts1[0] == sim_tts2[0]);
        //assert(sim_tts1[0] == sim_tts1_cegar[0]);
        //assert(sim_tts1_cegar[0] == sim_tts2_cegar[0]);
        assert(c1.satisfies_spec(spec));
        assert(c2.satisfies_spec(spec));
        
        printf("(%d/%d)\r", i+1, max_tests);
        fflush(stdout);
    }
    printf("\n");
}

/*******************************************************************************
    By default, does not check for full equivalence of all n-input functions.
    Users can specify a arbitrary runtime argument, which removes the limit on
    the number of equivalence tests.
*******************************************************************************/
int main(int argc, char **argv)
{
    bool full_coverage = false;
    if (argc > 1) {
        full_coverage = true;
    }
    if (full_coverage) {
        printf("Doing full equivalence check\n");
    } else {
        printf("Doing partial equivalence check\n");
    }
    
    check_std_equivalence<2>(full_coverage);
    check_std_equivalence<3>(full_coverage);
    check_std_equivalence<4>(full_coverage);

    return 0;
}

