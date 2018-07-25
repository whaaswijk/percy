#include <cstdio>
#include <percy/percy.hpp>
#include <chrono>

#define MAX_TESTS 256

using namespace percy;
using kitty::dynamic_truth_table;

/*******************************************************************************
    Verifies that our synthesizers' results are equivalent to each other.
*******************************************************************************/
void check_pf_equivalence(int nr_in, int FI, bool full_coverage)
{
    spec spec;

    bsat_wrapper solver;
    knuth_encoder encoder1(solver);
    knuth_fence2_encoder fence_encoder(solver);
    fence_encoder.reset_sim_tts(nr_in);

    // don't run too many tests.
    auto max_tests = (1 << (1 << nr_in));
    if (!full_coverage) {
        max_tests = std::min(max_tests, MAX_TESTS);
    }
    dynamic_truth_table tt(nr_in);

    chain c1, c2, c2_cegar, c3;

    int64_t total_elapsed1 = 0;
    int64_t total_elapsed2 = 0;
    int64_t total_elapsed3 = 0;
    int64_t total_elapsed4 = 0;

    for (auto i = 1; i < max_tests; i++) {
        kitty::create_from_words(tt, &i, &i+1);

        spec.verbosity = 0;
        spec.add_lex_func_clauses = true;
        spec[0] = tt;
        auto start = std::chrono::steady_clock::now();
        auto res1 = synthesize(spec, c1, solver, encoder1, SYNTH_STD_CEGAR);
        auto elapsed1 = std::chrono::duration_cast<std::chrono::microseconds>(
                std::chrono::steady_clock::now() - start
            ).count();
        assert(res1 == success);
        auto sim_tts1 = c1.simulate();
        auto c1_nr_vertices = c1.get_nr_steps();
        assert(c1.satisfies_spec(spec));

        //spec.verbosity = 2;
        spec.add_lex_func_clauses = false;
        start = std::chrono::steady_clock::now();
        auto res2 = pf_fence_synthesize(spec, c2);
        auto elapsed2 = std::chrono::duration_cast<std::chrono::microseconds>(
                std::chrono::steady_clock::now() - start
            ).count();
        assert(res2 == success);
        assert(c2.satisfies_spec(spec));
        auto sim_tts2 = c2.simulate();
        auto c2_nr_vertices = c2.get_nr_steps();
        assert(c1_nr_vertices == c2_nr_vertices);
        assert(sim_tts1[0] == sim_tts2[0]);

        start = std::chrono::steady_clock::now();
        auto res3 = pf_fence_synthesize(spec, c2_cegar);
        auto elapsed3 = std::chrono::duration_cast<std::chrono::microseconds>(
                std::chrono::steady_clock::now() - start
            ).count();
        assert(res3 == success);
        assert(c2_cegar.satisfies_spec(spec));
        const auto sim_tts2_cegar = c2_cegar.simulate();
        const auto c2_cegar_nr_vertices = c2_cegar.get_nr_steps();
        assert(c1_nr_vertices == c2_cegar_nr_vertices);
        assert(sim_tts1[0] == sim_tts2_cegar[0]);

        start = std::chrono::steady_clock::now();
        auto res4 = fence_cegar_synthesize(spec, c3, solver, fence_encoder);
        auto elapsed4 = std::chrono::duration_cast<std::chrono::microseconds>(
                std::chrono::steady_clock::now() - start
            ).count();
        assert(res4 == success);
        assert(c3.satisfies_spec(spec));
        const auto sim_tts3 = c3.simulate();
        const auto c3_nr_vertices = c3.get_nr_steps();
        assert(c1_nr_vertices == c3_nr_vertices);
        assert(sim_tts1[0] == sim_tts3[0]);
        
        printf("(%d/%d)\r", i+1, max_tests);
        fflush(stdout);
        total_elapsed1 += elapsed1;
        total_elapsed2 += elapsed2;
        total_elapsed3 += elapsed3;
        total_elapsed4 += elapsed4;
    }
    printf("\n");
    printf("Time elapsed (STD): %lldus\n", total_elapsed1);
    printf("Time elapsed (FENCE): %lldus\n", total_elapsed4);
    printf("Time elapsed (PF): %lldus\n", total_elapsed2);
    printf("Time elapsed (PF CEGAR): %lldus\n", total_elapsed3);
}

void check_pf_equivalence5()
{
    spec spec;

    bsat_wrapper solver;
    knuth_encoder encoder1(solver);
    knuth_fence2_encoder fence_encoder(solver);
    fence_encoder.reset_sim_tts(5);

    // don't run too many tests.
    auto max_tests = MAX_TESTS;
    dynamic_truth_table tt(5);

    chain c1, c2, c3;

    int64_t total_elapsed1 = 0;
    int64_t total_elapsed2 = 0;
    int64_t total_elapsed3 = 0;
        
    auto nr_instances = 0;

    for (auto i = 1; i < max_tests; i++) {
        kitty::create_from_words(tt, &i, &i+1);
        spec.add_lex_func_clauses = true;
        spec[0] = tt;
        auto start = std::chrono::steady_clock::now();
        auto res1 = synthesize(spec, c1, solver, encoder1, SYNTH_STD_CEGAR);
        auto elapsed1 = std::chrono::duration_cast<std::chrono::microseconds>(
                std::chrono::steady_clock::now() - start
            ).count();
        assert(res1 == success);
        auto sim_tts1 = c1.simulate();
        auto c1_nr_vertices = c1.get_nr_steps();
        assert(c1.satisfies_spec(spec));

        spec.add_lex_func_clauses = false;

        start = std::chrono::steady_clock::now();
        auto res2 = fence_cegar_synthesize(spec, c2, solver, fence_encoder);
        auto elapsed2 = std::chrono::duration_cast<std::chrono::microseconds>(
                std::chrono::steady_clock::now() - start
            ).count();
        assert(res2 == success);
        assert(c2.satisfies_spec(spec));
        auto sim_tts2 = c2.simulate();
        auto c2_nr_vertices = c2.get_nr_steps();
        assert(c1_nr_vertices == c2_nr_vertices);
        assert(sim_tts1[0] == sim_tts2[0]);

        start = std::chrono::steady_clock::now();
        auto res3 = pf_fence_synthesize(spec, c3);
        auto elapsed3 = std::chrono::duration_cast<std::chrono::microseconds>(
                std::chrono::steady_clock::now() - start
            ).count();
        assert(res3 == success);
        assert(c3.satisfies_spec(spec));
        auto sim_tts3 = c3.simulate();
        auto c3_nr_vertices = c3.get_nr_steps();
        assert(c1_nr_vertices == c3_nr_vertices);
        assert(sim_tts1[0] == sim_tts3[0]);

        printf("(%d/%d)\r", i+1, max_tests);
        fflush(stdout);
        total_elapsed1 += elapsed1;
        total_elapsed2 += elapsed2;
        total_elapsed3 += elapsed3;
    }
    printf("\n");
    printf("total instances synthesized: %d\n", nr_instances);
    printf("Time elapsed (STD): %lldus\n", total_elapsed1);
    printf("Time elapsed (FENCE): %lldus\n", total_elapsed2);
    printf("Time elapsed (PF): %lldus\n", total_elapsed3);
}

int main()
{
    bool full_coverage = false;
    if (full_coverage) {
        printf("Doing full equivalence check\n");
    } else {
        printf("Doing partial equivalence check\n");
    }

    check_pf_equivalence(2, 2, full_coverage);
    check_pf_equivalence(3, 2, full_coverage);
    check_pf_equivalence(4, 2, full_coverage);
    check_pf_equivalence5();
    
    return 0;
}

