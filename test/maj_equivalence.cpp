#include <cstdio>
#include <percy/percy.hpp>
#include <chrono>

#define MAX_TESTS 256

using namespace percy;
using kitty::dynamic_truth_table;


int main()
{
    {
        // Synthesize MAJ-3
        mig mig;
        spec spec;
        bsat_wrapper solver;
        maj_encoder encoder(solver);
        kitty::dynamic_truth_table tt(3);
        kitty::create_majority(tt);
        spec[0] = tt;

        auto start = std::chrono::steady_clock::now();
        auto res = mig_synthesize(spec, mig, solver, encoder);
        const auto elapsed = std::chrono::duration_cast<std::chrono::microseconds>(
                std::chrono::steady_clock::now() - start
            ).count();
        assert(res == success);
        assert(mig.satisfies_spec(spec));
        assert(mig.get_nr_steps() == 1);

        start = std::chrono::steady_clock::now();
        res = mig_fence_synthesize(spec, mig, solver, encoder);
        const auto elapsed_fence = std::chrono::duration_cast<std::chrono::microseconds>(
                std::chrono::steady_clock::now() - start
            ).count();
        assert(res == success);
        assert(mig.satisfies_spec(spec));
        assert(mig.get_nr_steps() == 1);

        start = std::chrono::steady_clock::now();
        res = mig_fence_cegar_synthesize(spec, mig, solver, encoder);
        const auto elapsed_fence_cegar = std::chrono::duration_cast<std::chrono::microseconds>(
                std::chrono::steady_clock::now() - start
            ).count();
        assert(res == success);
        assert(mig.satisfies_spec(spec));
        assert(mig.get_nr_steps() == 1);

        printf("MAJ-3 time elapsed (MIG): %lldus\n", elapsed);
        printf("MAJ-3 time elapsed (MIG FENCE): %lldus\n", elapsed_fence);
        printf("MAJ-3 time elapsed (MIG FENCE CEGAR): %lldus\n", elapsed_fence_cegar);
    }
    {
        // Exact synthesis of MAJ-5
        mig mig;
        spec spec;
        bsat_wrapper solver;
        maj_encoder encoder(solver);
        kitty::dynamic_truth_table tt(5);
        kitty::create_majority(tt);
        spec[0] = tt;

        auto start = std::chrono::steady_clock::now();
        auto res = mig_synthesize(spec, mig, solver, encoder);
        const auto elapsed = std::chrono::duration_cast<std::chrono::microseconds>(
                std::chrono::steady_clock::now() - start
            ).count();
        assert(res == success);
        assert(mig.satisfies_spec(spec));
        assert(mig.get_nr_steps() == 4);

        start = std::chrono::steady_clock::now();
        res = mig_fence_synthesize(spec, mig, solver, encoder);
        const auto fence_elapsed = std::chrono::duration_cast<std::chrono::microseconds>(
                std::chrono::steady_clock::now() - start
            ).count();
        assert(res == success);
        assert(mig.satisfies_spec(spec));
        assert(mig.get_nr_steps() == 4);

        start = std::chrono::steady_clock::now();
        res = mig_fence_cegar_synthesize(spec, mig, solver, encoder);
        const auto fence_cegar_elapsed = std::chrono::duration_cast<std::chrono::microseconds>(
                std::chrono::steady_clock::now() - start
            ).count();
        assert(res == success);
        assert(mig.satisfies_spec(spec));
        assert(mig.get_nr_steps() == 4);

        start = std::chrono::steady_clock::now();
        res = parallel_maj_synthesize(spec, mig);
        const auto parr_elapsed = std::chrono::duration_cast<std::chrono::microseconds>(
                std::chrono::steady_clock::now() - start
            ).count();
        assert(res == success);
        assert(mig.satisfies_spec(spec));
        assert(mig.get_nr_steps() == 4);

        printf("MAJ-5 time elapsed (MIG): %lldus\n", elapsed);
        printf("MAJ-5 time elapsed (MIG FENCE): %lldus\n", fence_elapsed);
        printf("MAJ-5 time elapsed (MIG FENCE CEGAR): %lldus\n", fence_cegar_elapsed);
        printf("MAJ-5 time elapsed (MIG PARR): %lldus\n", parr_elapsed);
    }

    {
        // Exact synthesis of MAJ-7
        mig mig;
        spec spec;
        bsat_wrapper solver;
        maj_encoder encoder(solver);
        kitty::dynamic_truth_table tt(7);
        kitty::create_majority(tt);
        spec[0] = tt;

        /*
        auto start = std::chrono::steady_clock::now();
        auto res = mig_synthesize(spec, mig, solver, encoder);
        const auto elapsed = std::chrono::duration_cast<std::chrono::microseconds>(
                std::chrono::steady_clock::now() - start
            ).count();
        assert(res == success);
        assert(mig.satisfies_spec(spec));
        assert(mig.get_nr_steps() == 7);
        printf("MAJ-7 time elapsed (MIG): %lldus\n", elapsed);

        auto start = std::chrono::steady_clock::now();
        auto res = mig_fence_synthesize(spec, mig, solver, encoder);
        const auto fence_elapsed = std::chrono::duration_cast<std::chrono::microseconds>(
                std::chrono::steady_clock::now() - start
            ).count();
        assert(res == success);
        assert(mig.satisfies_spec(spec));
        assert(mig.get_nr_steps() == 7);
        printf("MAJ-7 time elapsed (MIG FENCE): %lldus\n", fence_elapsed);
        auto start = std::chrono::steady_clock::now();
        auto res = parallel_maj_synthesize(spec, mig);
        const auto parr_elapsed = std::chrono::duration_cast<std::chrono::microseconds>(
                std::chrono::steady_clock::now() - start
            ).count();
        assert(res == success);
        assert(mig.satisfies_spec(spec));
        assert(mig.get_nr_steps() == 7);
        printf("MAJ-7 time elapsed (MIG PARR): %lldus\n", parr_elapsed);


        spec.verbosity = 1;
        start = std::chrono::steady_clock::now();
        res = mig_fence_cegar_synthesize(spec, mig, solver, encoder);
        const auto fence_cegar_elapsed = std::chrono::duration_cast<std::chrono::microseconds>(
                std::chrono::steady_clock::now() - start
            ).count();
        assert(res == success);
        assert(mig.satisfies_spec(spec));
        assert(mig.get_nr_steps() == 7);
        printf("MAJ-7 time elapsed (MIG FENCE CEGAR): %lldus\n", fence_cegar_elapsed);
        */
    }
    
    return 0;
}

