#include <cstdio>
#include <percy/percy.hpp>
#include <kitty/kitty.hpp>

#define MAX_TESTS 256

using namespace percy;
using kitty::static_truth_table;

/*******************************************************************************
    Verifies that our synthesizers' results are equivalent to each other.
*******************************************************************************/
template<int nr_in>
void check_equivalence(bool full_coverage)
{
    synth_spec<static_truth_table<nr_in>> spec(nr_in, 1);
    std_synthesizer<> synth1;
    std_synthesizer<3> synth2;
    std_synthesizer<4> synth3;

    spec.verbosity = 0;

    // don't run too many tests.
    auto max_tests = (1 << (1 << nr_in));
    if (!full_coverage) {
        max_tests = std::min(max_tests, MAX_TESTS);
    }
    static_truth_table<nr_in> tt;

    chain<2> c1, c1_cegar;
    chain<3> c2, c2_cegar;
    chain<4> c3, c3_cegar;

    for (auto i = 1; i < max_tests; i++) {
        kitty::create_from_words(tt, &i, &i+1);

        spec.functions[0] = &tt;
        auto res1 = synth1.synthesize(spec, c1);
        assert(res1 == success);
        auto sim_tts1 = c1.template simulate(spec);

        auto res1_cegar = synth1.cegar_synthesize(spec, c1_cegar);
        assert(res1_cegar == success);
        auto sim_tts1_cegar = c1_cegar.template simulate(spec);

        auto res2 = synth2.synthesize(spec, c2);
        assert(res2 == success);
        auto sim_tts2 = c2.template simulate(spec);
        auto c2_nr_vertices = c2.get_nr_vertices();

        auto res2_cegar = synth2.cegar_synthesize(spec, c2_cegar);
        assert(res2_cegar == success);
        auto sim_tts2_cegar = c2_cegar.template simulate(spec);
        auto c2_cegar_nr_vertices = c2.get_nr_vertices();

        assert(c2_nr_vertices == c2_cegar_nr_vertices);
        assert(sim_tts1[0] == sim_tts2[0]);
        assert(sim_tts1[0] == sim_tts1_cegar[0]);
        assert(sim_tts1_cegar[0] == sim_tts2_cegar[0]);

        if (nr_in >= 4) {
            auto res3 = synth3.synthesize(spec, c3);
            assert(res3 == success);
            auto sim_tts3 = c3.template simulate(spec);
            auto c3_nr_vertices = c3.get_nr_vertices();

            auto res3_cegar = synth3.cegar_synthesize(spec, c3_cegar);
            assert(res3_cegar == success);
            auto sim_tts3_cegar = c3_cegar.template simulate(spec);
            auto c3_cegar_nr_vertices = c3.get_nr_vertices();

            assert(c3_nr_vertices == c3_cegar_nr_vertices);
            assert(sim_tts3[0] == sim_tts2[0]);
            assert(sim_tts3_cegar[0] == sim_tts2[0]);
        }
        
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

    //check_equivalence<2>(full_coverage);
    check_equivalence<3>(full_coverage);
    check_equivalence<4>(full_coverage);
    
    return 0;
}

