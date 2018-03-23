#include <percy/percy.hpp>

#define MAX_TESTS 512

using namespace percy;


/*******************************************************************************
    Tests if parallel fence based synthesis works correctly.
*******************************************************************************/

template<int nrin>
void check_equivalence()
{
    dag<2> g;
    unbounded_dag_generator<sat_solver*> ugen;

    synth_stats stats;
    synth_spec<static_truth_table<nrin>> spec;
    auto synth1 = new_synth<static_truth_table<nrin>,sat_solver*>(SYMMETRIC);
    dag_synthesizer<static_truth_table<nrin>,sat_solver*> synth2;

    spec.nr_in = nrin;
    spec.nr_out = 1;
    spec.verbosity = 0;

    // don't run too many tests.
    auto max_tests = (1 << (1 << nrin));
    max_tests = std::min(max_tests, MAX_TESTS);
    static_truth_table<nrin> tt;

    chain<static_truth_table<nrin>> c1;
    chain<static_truth_table<nrin>> c2;

    printf("Testing %d-input equivalence\n", nrin);

    for (auto i = 1; i < max_tests; i++) {
        kitty::create_from_words(tt, &i, &i+1);

        // We skip the trivial functions
        if (is_trivial(tt)) {
            continue;
        }
        spec.functions[0] = &tt;
        auto res1 = synth1->synthesize(spec, c1);
        assert(res1 == success);
        auto sim_tts1 = c1.simulate();
        auto c1_nr_steps = c1.nr_steps();

        auto res2 = qpfence_synth(&stats, tt, g, nrin, 0);
        assert(res2 == success);
        // Make sure that the found DAG is indeed valid for this function.
        synth2.reset(nrin, g.get_nr_vertices());
        synth2.synthesize(tt, g, c2);
        auto sim_tts2 = c2.simulate();
        auto c2_nr_steps = c2.nr_steps();

        assert(*sim_tts1[0] == *sim_tts2[0]);
        assert(c1_nr_steps == c2_nr_steps);
        printf("(%d/%d)\r", i+1, max_tests);
        fflush(stdout);
    } 
    printf("\n");
}


int main(void)
{
    check_equivalence<2>();
    check_equivalence<3>();
    check_equivalence<4>();

    return 0;
}

