#include <percy/percy.hpp>
#include <chrono>
#include <thread>

#define MAX_TESTS 512

using namespace percy;
using kitty::static_truth_table;

/*******************************************************************************
    In this module, we test the equivalence of the sequential and parallel
    find_dag implementations.
*******************************************************************************/

template<int nrin>
auto
get_npn_classes()
{
    std::unordered_set<static_truth_table<nrin>, kitty::hash<static_truth_table<nrin>>> classes;
    static_truth_table<1 << nrin> map;
    std::transform(map.cbegin(), map.cend(), map.begin(), 
            []( auto w ) { return ~w; } );

    int64_t index = 0;
    static_truth_table<nrin> tt;
    while (index != -1) {
        kitty::create_from_words(tt, &index, &index + 1);
        const auto res = kitty::exact_npn_canonization(
                tt, [&map]( const auto& tt ) { 
                    kitty::clear_bit( map, *tt.cbegin() ); 
                } 
            );
        classes.insert( std::get<0>( res ) );
        index = find_first_one_bit( map );
    }

    printf("[i] enumerated %lu functions into %lu classes\n",
            map.num_bits(), classes.size());

    return classes;
}

template<int nrin>
void check_npn_equivalence()
{
    dag<2> g1, g2;
    
    auto npn_set = get_npn_classes<nrin>();
    const auto num_cpus = std::thread::hardware_concurrency();

    int i = 1;
    const auto total = npn_set.size();
    for (auto& npn_tt : npn_set) {
        static_truth_table<nrin> tt = npn_tt;

        // We skip the trivial functions
        if (is_trivial(tt)) {
            printf("(%d/%d)\r", i++, total);
            fflush(stdout);
            continue;
        }

        auto seq_start = std::chrono::high_resolution_clock::now();
        auto seq_result = find_dag(tt, g1, nrin);
        auto seq_stop = std::chrono::high_resolution_clock::now();
    
        auto qpar_start = std::chrono::high_resolution_clock::now();
        auto qpar_result = qpfind_dag<static_truth_table<nrin>>(
                tt, g2, nrin);
        auto qpar_stop = std::chrono::high_resolution_clock::now();

        assert(seq_result == success);
        assert(qpar_result == success);
        assert(g1.get_nr_vertices() == g2.get_nr_vertices());

        printf("Time elapsed: %fms (SEQ)\n", 
            std::chrono::duration<double,std::milli>(
                seq_stop-seq_start).count());
        printf("Time elapsed: %fms (QPAR)\n", 
            std::chrono::duration<double,std::milli>(
                qpar_stop-qpar_start).count());
            
        printf("(%d/%d)\r", i++, total);
        fflush(stdout);
    }
    printf("\n");
}

int main(void)
{
    const auto num_cpus = std::thread::hardware_concurrency();

// TODO: fix Travis errors.
#ifndef TRAVIS_BUILD
    check_npn_equivalence<2>();
    check_npn_equivalence<3>();
    if (num_cpus >= 6) {
        check_npn_equivalence<4>();
    }
#endif
    
    return 0;
}

