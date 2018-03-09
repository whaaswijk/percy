#include <cstdio>
#include <percy/percy.hpp>
#include <kitty/kitty.hpp>

#define MAX_TESTS 512

using namespace percy;
using kitty::static_truth_table;

/*******************************************************************************
    Verifies that synthesizing Boolean chains with 3-input operators yields
    the expected results.
*******************************************************************************/
template<template<typename,typename,int> class S, 
    int NrIn, typename Solver=sat_solver*>
void check_equivalence(bool full_coverage)
{
    synth_spec<static_truth_table<NrIn>,Solver> spec1;
    synth_spec<static_truth_table<NrIn>,Solver> spec2;
    S<static_truth_table<NrIn>,Solver,2> synth1;
    S<static_truth_table<NrIn>,Solver,3> synth2;

    chain<static_truth_table<NrIn>,2> c1;
    chain<static_truth_table<NrIn>,3> c2;

    spec1.nr_in = spec2.nr_in = NrIn;
    spec1.nr_out = spec2.nr_out = 1;
    spec1.verbosity = spec2.verbosity = 0;

    // Don't run too many tests.
    auto max_tests = (1 << (1 << NrIn));
    if (!full_coverage) {
        max_tests = std::min(max_tests, MAX_TESTS);
    }
    static_truth_table<NrIn> tt;
    for (auto i = 1; i < max_tests; i++) {
        kitty::create_from_words(tt, &i, &i+1);

        spec1.functions[0] = &tt;
        spec2.functions[0] = &tt;

        auto res1 = synth1.synthesize(spec1, c1);
        assert(res1 == success);

        auto res2 = synth2.synthesize3(spec2, c2);
        assert(res2 == success);

        if (NrIn == 3) {
            assert(c2.nr_steps() <= 1);
        }

        auto sim_tts1 = c1.simulate();
        auto sim_tts2 = c2.simulate();

        assert(*sim_tts1[0] == *sim_tts2[0]);
    }
}

template<
    template<typename,typename,int> class S1, 
    template<typename,typename,int> class S2, 
    int NrIn, typename Solver=sat_solver*>
void check_synth3_equivalence(bool full_coverage)
{
    synth_spec<static_truth_table<NrIn>,Solver> spec;
    S1<static_truth_table<NrIn>,Solver,3> synth1;
    S2<static_truth_table<NrIn>,Solver,3> synth2;

    spec.nr_in = NrIn;
    spec.nr_out = 1;
    spec.verbosity = 0;

    chain<static_truth_table<NrIn>,3> c1;
    chain<static_truth_table<NrIn>,3> c2;

    // Don't run too many tests.
    auto max_tests = (1 << (1 << NrIn));
    if (!full_coverage) {
        max_tests = std::min(max_tests, MAX_TESTS);
    }
    static_truth_table<NrIn> tt;
    for (auto i = 1; i < max_tests; i++) {
        kitty::create_from_words(tt, &i, &i+1);

        spec.functions[0] = &tt;

        auto res1 = synth1.synthesize3(spec, c1);
        assert(res1 == success);
        auto sim_tts1 = c1.simulate();
        auto c1_nr_steps = c1.nr_steps();

        auto res1_cegar = synth1.cegar_synthesize3(spec, c1);
        assert(res1_cegar == success);
        auto sim_tts1_cegar = c1.simulate();
        auto c1_cegar_nr_steps = c1.nr_steps();

        auto res2 = synth2.synthesize3(spec, c2);
        assert(res2 == success);
        auto sim_tts2 = c2.simulate();
        auto c2_nr_steps = c2.nr_steps();

        auto res2_cegar = synth2.cegar_synthesize3(spec, c2);
        assert(res2_cegar == success);
        auto sim_tts2_cegar = c2.simulate();
        auto c2_cegar_nr_steps = c2.nr_steps();

        assert(c1_nr_steps == c2_nr_steps);
        assert(c2_nr_steps == c1_cegar_nr_steps);
        assert(c2_cegar_nr_steps == c1_cegar_nr_steps);

        assert(*sim_tts1[0] == *sim_tts2[0]);
        assert(*sim_tts1[0] == *sim_tts1_cegar[0]);
        assert(*sim_tts1_cegar[0] == *sim_tts2_cegar[0]);
    }
}

template<
    template<typename,typename,int> class s1, 
    int nrin, typename solver=sat_solver*>
void check_equivalence_parallel3(bool full_coverage)
{
    synth_spec<static_truth_table<nrin>,solver> spec;
    s1<static_truth_table<nrin>,solver,3> synth;

    spec.nr_in = nrin;
    spec.nr_out = 1;
    spec.verbosity = 0;

    // Don't run too many tests.
    auto max_tests = (1 << (1 << nrin));
    if (!full_coverage) {
        max_tests = std::min(max_tests, MAX_TESTS);
    }
    static_truth_table<nrin> tt;

    chain<static_truth_table<nrin>,3> c1_cegar;
    chain<static_truth_table<nrin>,3> c2;
    chain<static_truth_table<nrin>,3> c2_cegar;

    for (auto i = 1; i < max_tests; i++) {
        kitty::create_from_words(tt, &i, &i+1);

        spec.functions[0] = &tt;

        auto res1_cegar = synth.cegar_synthesize3(spec, c1_cegar);
        assert(res1_cegar == success);
        auto sim_tts1_cegar = c1_cegar.simulate();
        auto c1_cegar_nr_steps = c1_cegar.nr_steps();

        auto res2 = synthesize_parallel3(spec, 4, c2);
        assert(res2 == success);
        auto sim_tts2 = c2.simulate();
        auto c2_nr_steps = c2.nr_steps();

        auto res2_cegar = cegar_synthesize_parallel3(spec, 4, c2_cegar);
        assert(res2_cegar == success);
        auto sim_tts2_cegar = c2_cegar.simulate();
        auto c2_cegar_nr_steps = c2_cegar.nr_steps();

        assert(c1_cegar_nr_steps == c2_nr_steps);
        assert(c1_cegar_nr_steps == c2_cegar_nr_steps);
        assert(*sim_tts1_cegar[0] == *sim_tts2[0]);
        assert(*sim_tts1_cegar[0] == *sim_tts2_cegar[0]);
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
    
    /*
    check_equivalence<simple_synthesizer,3>(full_coverage);
    check_equivalence<simple_synthesizer,4>(full_coverage);
    */
    
    check_equivalence_parallel3<top_synthesizer,3>(full_coverage);
    check_equivalence_parallel3<top_synthesizer,4>(full_coverage);

    check_synth3_equivalence<colex_synthesizer,top_synthesizer,3>(full_coverage);
    check_synth3_equivalence<colex_synthesizer,top_synthesizer,4>(full_coverage);
    check_synth3_equivalence<colex_synthesizer,top_synthesizer,5>(full_coverage);
    
    check_synth3_equivalence<noreapply_synthesizer,colex_synthesizer,3>(full_coverage);
    check_synth3_equivalence<noreapply_synthesizer,colex_synthesizer,4>(full_coverage);
    check_synth3_equivalence<noreapply_synthesizer,colex_synthesizer,5>(full_coverage);
    
    check_synth3_equivalence<alonce_synthesizer,noreapply_synthesizer,3>(full_coverage);
    check_synth3_equivalence<alonce_synthesizer,noreapply_synthesizer,4>(full_coverage);
    check_synth3_equivalence<alonce_synthesizer,noreapply_synthesizer,5>(full_coverage);
    
    check_synth3_equivalence<nontriv_synthesizer,alonce_synthesizer,3>(full_coverage);
    check_synth3_equivalence<nontriv_synthesizer,alonce_synthesizer,4>(full_coverage);
    check_synth3_equivalence<nontriv_synthesizer,alonce_synthesizer,5>(full_coverage);
    
    check_synth3_equivalence<simple_synthesizer,nontriv_synthesizer,3>(full_coverage);
    check_synth3_equivalence<simple_synthesizer,nontriv_synthesizer,4>(full_coverage);
    check_synth3_equivalence<simple_synthesizer,nontriv_synthesizer,5>(full_coverage);

    return 0;
}

