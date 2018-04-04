#include <cstdio>
#include <percy/percy.hpp>
#include <kitty/kitty.hpp>
#include <ctime>

#define NR_IN 5
#define NR_FUNCS 2

using namespace percy;

/*******************************************************************************
    Verifies that our timeouts work correctly.
*******************************************************************************/
template<int NrIn, template<int, typename, typename> class Synth>
void check_timeout(static_truth_table<NrIn>& tt, int conflict_limit, vector<double>& times)
{
    synth_spec<static_truth_table<NrIn>> spec;
    spec.set_nr_in(NrIn);
    spec.set_nr_out(1);
    spec.conflict_limit = conflict_limit;
    spec.functions[0] = &tt;
    spec.verbosity = 0;
    
    auto synth = new_fence_synth();

    chain<2> chain;
    auto start = std::clock();
    auto res = synth->synthesize(spec, chain);
    auto elapsed = std::clock()-start;
    times.push_back(elapsed / (double) CLOCKS_PER_SEC);
    assert(res == timeout);
    //assert(solver_nr_conflicts(spec.solver()) >= conflict_limit);
}

int main(void)
{
    kitty::static_truth_table<5> tt;
    vector<double> times;
    for (int i = 0; i < NR_FUNCS; i++) {
        kitty::create_random(tt);
        check_timeout<NR_IN, fence_synthesizer>(tt, 100000, times);
    }

    for (int i = 0; i < NR_FUNCS; i++) {
        printf("time[%d] = %fs\n", i, times[i]);
    }
    
    auto tot = std::accumulate(times.rbegin(), times.rend(), 0.0);
    printf("Total elapsed time = %fs\n", tot);
    auto mean = tot / NR_FUNCS;
    printf("Mean time per function = %fs\n", mean);
    double sq_sum = std::inner_product(times.begin(), times.end(), times.begin(), 0.0);
    double stdev = std::sqrt(sq_sum / NR_FUNCS - mean * mean);
    printf("Standard deviation = %fs\n", stdev);

    return 0;
}

