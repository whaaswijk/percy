#include <cstdio>
#include <percy/percy.hpp>
#include <kitty/kitty.hpp>

#define MAX_TESTS 256

using namespace percy;
using kitty::dynamic_truth_table;

/*******************************************************************************
    Verifies that our synthesizers' results are equivalent to each other.
*******************************************************************************/
void check_fence_equivalence(int nr_in, int FI, bool full_coverage)
{
    spec spec;
    spec.verbosity = 0;

    bsat_wrapper solver;
    knuth_encoder encoder1(solver);
    knuth_fence_encoder encoder2(solver);

    // don't run too many tests.
    auto max_tests = (1 << (1 << nr_in));
    if (!full_coverage) {
        max_tests = std::min(max_tests, MAX_TESTS);
    }
    dynamic_truth_table tt(nr_in);

    chain c1, c1_cegar, c2, c2_cegar;

    for (auto i = 1; i < max_tests; i++) {
        kitty::create_from_words(tt, &i, &i+1);

        spec[0] = tt;
        auto res1 = synthesize(spec, c1, solver, encoder1, SYNTH_STD);
        assert(res1 == success);
        auto sim_tts1 = c1.simulate(spec);
        auto c1_nr_vertices = c1.get_nr_steps();
        assert(c1.satisfies_spec(spec));

        auto res1_cegar = synthesize(spec, c1_cegar, solver, encoder1, SYNTH_STD_CEGAR);
        assert(res1_cegar == success);
        auto sim_tts1_cegar = c1_cegar.simulate(spec);
        auto c1_cegar_nr_vertices = c1_cegar.get_nr_steps();
        assert(c1_cegar.satisfies_spec(spec));

        auto res2 = synthesize(spec, c2, solver, encoder2, SYNTH_FENCE);
        assert(res2 == success);
        auto sim_tts2 = c2.simulate(spec);
        auto c2_nr_vertices = c2.get_nr_steps();
        // TODO: Re-enable check once additional constraints have been added
        // to fence-based synthesis.
        //assert(c2.satisfies_spec(spec));

        auto res2_cegar = synthesize(spec, c2_cegar, solver, encoder2, SYNTH_FENCE_CEGAR);
        assert(res2_cegar == success);
        auto sim_tts2_cegar = c2_cegar.simulate(spec);
        auto c2_cegar_nr_vertices = c2.get_nr_steps();
        // TODO: re-enable
        //assert(c2_cegar.satisfies_spec(spec));

        assert(c1_nr_vertices == c2_nr_vertices);
        assert(c1_nr_vertices == c1_cegar_nr_vertices);
        assert(c1_cegar_nr_vertices == c2_cegar_nr_vertices);
        assert(sim_tts1[0] == sim_tts2[0]);
        assert(sim_tts1[0] == sim_tts1_cegar[0]);
        assert(sim_tts1_cegar[0] == sim_tts2_cegar[0]);
        
        printf("(%d/%d)\r", i+1, max_tests);
        fflush(stdout);
    }
    printf("\n");
}


/*******************************************************************************
    Verifies that parallel synthesis behaves as expected.
*******************************************************************************
template<
    template<typename,typename> class s1, 
    int nr_in, typename solver=sat_solver*>
void check_equivalence_parallel(bool full_coverage)
{
    synth_spec<static_truth_table<nr_in>> spec;
    auto synth = new_synth<s1<static_truth_table<nr_in>,solver>>();

    spec.nr_in = nr_in;
    spec.nr_out = 1;
    spec.verbosity = 0;

    // Don't run too many tests.
    auto max_tests = (1 << (1 << nr_in));
    if (!full_coverage) {
        max_tests = std::min(max_tests, MAX_TESTS);
    }
    static_truth_table<nr_in> tt;

    chain<static_truth_table<nr_in>> c1_cegar;
    chain<static_truth_table<nr_in>> c2;
    chain<static_truth_table<nr_in>> c2_cegar;

    for (auto i = 1; i < max_tests; i++) {
        kitty::create_from_words(tt, &i, &i+1);

        spec.functions[0] = &tt;

        auto res1_cegar = synth->cegar_synthesize(spec, c1_cegar);
        assert(res1_cegar == success);
        auto sim_tts1_cegar = c1_cegar.simulate();
        auto c1_cegar_nr_vertices = c1_cegar.get_nr_steps();

        auto res2 =
            synthesize_parallel<static_truth_table<nr_in>, solver>(spec, 4, c2);
        assert(res2 == success);
        auto sim_tts2 = c2.simulate();
        auto c2_nr_vertices = c2.get_nr_steps();

        auto res2_cegar = 
            cegar_synthesize_parallel<static_truth_table<nr_in>, solver>(spec, 
                    4, c2_cegar);
        assert(res2_cegar == success);
        auto sim_tts2_cegar = c2_cegar.simulate();
        auto c2_cegar_nr_vertices = c2_cegar.get_nr_steps();

        assert(c1_cegar_nr_vertices == c2_nr_vertices);
        assert(c1_cegar_nr_vertices == c2_cegar_nr_vertices);
        assert(*sim_tts1_cegar[0] == *sim_tts2[0]);
        assert(*sim_tts1_cegar[0] == *sim_tts2_cegar[0]);
    }
    printf("\n");
}
*/


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

    /*
    check_equivalence_parallel<fence_synthesizer,2>(full_coverage);
    check_equivalence_parallel<fence_synthesizer,3>(full_coverage);
    check_equivalence_parallel<fence_synthesizer,4>(full_coverage);
    */
    
    check_fence_equivalence(2, 2, full_coverage);
    //check_equivalence<STD, DAG, 2>(full_coverage);

    check_fence_equivalence(3, 2, full_coverage);
    //check_equivalence<STD, DAG, 3>(full_coverage);
    
    check_fence_equivalence(4, 2, full_coverage);
    //check_equivalence<STD, DAG, 4>(full_coverage);
    
    /*
    check_equivalence<
        std_synthesizer<3>, 
        fence_synthesizer<3>, 
        2, 
        3>(full_coverage);
    */
    //check_equivalence<STD,DAG, 2, 3>(full_coverage);
    
    check_fence_equivalence(3, 3, full_coverage);
    //check_equivalence<STD,DAG, 3, 3>(full_coverage);
    
    check_fence_equivalence(4, 3, full_coverage);
    
    return 0;
}

