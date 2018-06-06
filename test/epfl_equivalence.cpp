#include <cstdio>
#include <percy/percy.hpp>
#include <kitty/kitty.hpp>

#define MAX_TESTS 256

using namespace percy;
using kitty::static_truth_table;

template<int nr_in, int FI=2>
void check_equivalence(bool full_coverage)
{
    synth_spec<static_truth_table<nr_in>> spec(nr_in, 1);
    std_synthesizer<FI, knuth_encoder<FI, sat_solver*>, sat_solver*> synth1;
    std_synthesizer<FI, epfl_encoder<FI, sat_solver*>, sat_solver*> synth2;

    spec.verbosity = 0;
    spec.add_nontriv_clauses = false;
    spec.add_alonce_clauses = false; ///< Symmetry break: all steps must be used at least once
    spec.add_noreapply_clauses = false; ///< Symmetry break: no re-application of operators
    spec.add_colex_clauses = false; ///< Symmetry break: order step fanins co-lexicographically
    spec.add_lex_func_clauses = false; ///< Symmetry break: order step operators co-lexicographically
    spec.add_symvar_clauses = false; ///< Symmetry break: impose order on symmetric variables
    spec.add_lex_clauses = false; ///< Symmetry break: order step fanins lexicographically

    // don't run too many tests.
    auto max_tests = (1 << (1 << nr_in));
    if (!full_coverage) {
        max_tests = std::min(max_tests, MAX_TESTS);
    }
    static_truth_table<nr_in> tt;

    chain<FI> c1, c1_cegar, c2, c2_cegar;

    for (auto i = 1; i < max_tests; i++) {
        kitty::create_from_words(tt, &i, &i+1);

        spec.functions[0] = &tt;
        auto res1 = synth1.synthesize(spec, c1);
        assert(res1 == success);
        auto sim_tts1 = c1.simulate(spec);
        auto c1_nr_vertices = c1.get_nr_vertices();
        assert(c1.satisfies_spec(spec));

        auto res1_cegar = synth1.cegar_synthesize(spec, c1_cegar);
        assert(res1_cegar == success);
        auto sim_tts1_cegar = c1_cegar.simulate(spec);
        auto c1_cegar_nr_vertices = c1_cegar.get_nr_vertices();
        assert(c1_cegar.satisfies_spec(spec));

        auto res2 = synth2.synthesize(spec, c2);
        assert(res2 == success);
        auto sim_tts2 = c2.simulate(spec);
        auto c2_nr_vertices = c2.get_nr_vertices();
        // TODO: Re-enable check once additional constraints have been added
        // to fence-based synthesis.
        //assert(c2.satisfies_spec(spec));

        auto res2_cegar = synth2.cegar_synthesize(spec, c2_cegar);
        assert(res2_cegar == success);
        auto sim_tts2_cegar = c2_cegar.simulate(spec);
        auto c2_cegar_nr_vertices = c2.get_nr_vertices();
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
    Verifies that the EPFL encoding is equivalent to the Knuth encoding.
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

    check_equivalence<2>(full_coverage);
    check_equivalence<3>(full_coverage);
    check_equivalence<4>(full_coverage);
    check_equivalence<3, 3>(full_coverage);
    check_equivalence<4, 3>(full_coverage);

    return 0;
}

