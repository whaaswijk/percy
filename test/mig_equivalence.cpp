#include <cstdio>
#include <percy/percy.hpp>
#include <chrono>

#define MAX_TESTS 256

using namespace percy;
using kitty::dynamic_truth_table;

/*******************************************************************************
    Verifies that our synthesizers' results are equivalent to each other.
*******************************************************************************/
void profile(int nr_in)
{
    spec spec;

    bsat_wrapper solver;
    mig_encoder encoder(solver);

    // don't run too many tests.
    auto max_tests = (1 << (1 << nr_in));
    max_tests = std::min(max_tests, MAX_TESTS);
    dynamic_truth_table tt(nr_in);

    mig m1;

    int64_t total_elapsed1 = 0;

    for (auto i = 1; i < max_tests; i++) {
        kitty::create_from_words(tt, &i, &i+1);
        if (nr_in < 3) {
            tt = kitty::extend_to(tt, 3);
        }

        spec.verbosity = 1;
        spec[0] = tt;
        //spec.verbosity = 2;

        spec.add_colex_clauses = false;
        spec.add_lex_func_clauses = false;
        spec.add_symvar_clauses = false;
        spec.add_noreapply_clauses = false;
        auto start = std::chrono::steady_clock::now();
        const auto res1 = mig_synthesize(spec, m1, solver, encoder);
        const auto elapsed1 = std::chrono::duration_cast<std::chrono::microseconds>(
                std::chrono::steady_clock::now() - start
            ).count();
        assert(res1 == success);
        assert(m1.satisfies_spec(spec));
        if (nr_in <= 3) {
            assert(m1.get_nr_steps() == 1);
        }

        total_elapsed1 += elapsed1;
    }
    printf("\n");
    printf("Time elapsed (MIG): %lldus\n", total_elapsed1);
}

void profile5(void)
{
    spec spec;

    bsat_wrapper solver;
    knuth_encoder encoder(solver);
    knuth_fence_encoder fence_encoder(solver);
    knuth_fence2_encoder fence2_encoder(solver);
    fence2_encoder.reset_sim_tts(5);

    // don't run too many tests.
    dynamic_truth_table tt(5);

    chain c1, c2, c3, c4;

    int64_t total_elapsed1 = 0;
    int64_t total_elapsed2 = 0;
    int64_t total_elapsed3 = 0;
    int64_t total_elapsed4 = 0;

    auto solved_instances = 0;

    for (auto i = 1; i < MAX_TESTS; i++) {
        kitty::create_from_words(tt, &i, &i+1);

        spec.verbosity = 0;
        spec[0] = tt;
        //spec.verbosity = 2;

        spec.add_colex_clauses = true;
        spec.add_lex_func_clauses = true;
        spec.add_symvar_clauses = true;
        spec.add_noreapply_clauses = true;
        auto start = std::chrono::steady_clock::now();
        const auto res1 = synthesize(spec, c1, solver, encoder);
        if (res1 == timeout) {
            continue;
        }
        solved_instances++;
        const auto elapsed1 = std::chrono::duration_cast<std::chrono::microseconds>(
                std::chrono::steady_clock::now() - start
            ).count();
        assert(res1 == success);
        assert(c1.satisfies_spec(spec));

        spec.add_colex_clauses = false;
        spec.add_lex_func_clauses = false;
        spec.add_symvar_clauses = false;
        spec.add_noreapply_clauses = false;
        start = std::chrono::steady_clock::now();
        const auto res2 = fence_synthesize(spec, c2, solver, fence_encoder);
        const auto elapsed2 = std::chrono::duration_cast<std::chrono::microseconds>(
                std::chrono::steady_clock::now() - start
            ).count();
        assert(res2 == success);
        assert(c2.satisfies_spec(spec));
        assert(c1.get_nr_steps() == c2.get_nr_steps());

        spec.add_colex_clauses = true;
        spec.add_lex_func_clauses = false;
        spec.add_symvar_clauses = true;
        spec.add_noreapply_clauses = true;

        start = std::chrono::steady_clock::now();
        const auto res3 = fence_synthesize(spec, c3, solver, fence2_encoder);
        const auto elapsed3 = std::chrono::duration_cast<std::chrono::microseconds>(
                std::chrono::steady_clock::now() - start
            ).count();
        assert(res3 == success);
        assert(c3.satisfies_spec(spec));
        assert(c1.get_nr_steps() == c3.get_nr_steps());

        start = std::chrono::steady_clock::now();
        const auto res4 = fence_cegar_synthesize(spec, c4, solver, fence2_encoder);
        const auto elapsed4 = std::chrono::duration_cast<std::chrono::microseconds>(
                std::chrono::steady_clock::now() - start
            ).count();
        assert(res4 == success);
        assert(c4.satisfies_spec(spec));
        assert(c1.get_nr_steps() == c4.get_nr_steps());
        
        printf("(%d/%d)\r", i+1, MAX_TESTS);
        fflush(stdout);

        total_elapsed1 += elapsed1;
        total_elapsed2 += elapsed2;
        total_elapsed3 += elapsed3;
        total_elapsed4 += elapsed4;
    }
    printf("\n");
    printf("Nr. of solved instances: (%d/%d)\n", solved_instances, MAX_TESTS);
    printf("Time elapsed (STD): %lldus\n", total_elapsed1);
    printf("Time elapsed (FENCE): %lldus\n", total_elapsed2);
    printf("Time elapsed (FENCE2): %lldus\n", total_elapsed3);
    printf("Time elapsed (FENCE2 CEGAR): %lldus\n", total_elapsed4);
}

int main()
{
    profile(2);
    profile(3);
    profile(4);
#ifndef TRAVIS_BUILD
//    profile5();
#endif
    
    return 0;
}

