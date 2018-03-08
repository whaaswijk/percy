#include <topsynth/topsynth.hpp>

#define MAX_TESTS 512ul

using namespace topsynth;
using kitty::static_truth_table;

template<int nrin>
void check_equivalence(bool full_coverage)
{
    printf("Checking synthesis equivalence for %d-input functions\n", nrin);

    dag g;
    vector<int> perm(nrin);
    static_truth_table<nrin> tt;
    chain<static_truth_table<nrin>> c1;
    chain<static_truth_table<nrin>> c2;
    unbounded_dag_generator<sat_solver*> ugen;
    nonisomorphic_dag_generator<sat_solver*> igen;
    dag_synthesizer<static_truth_table<nrin>,sat_solver*> synth;

    // don't run too many tests.
    auto max_tests = (1ul << (1ul << nrin));
    if (!full_coverage) {
        max_tests = std::min(max_tests, MAX_TESTS);
    }
    for (auto i = 1ul; i < max_tests; i++) {
        printf("i = %lu\n", i);
        kitty::create_from_words(tt, &i, &i+1);

        // We skip the trivial functions
        if (is_trivial(tt)) {
            continue;
        }

        ugen.reset(nrin);
        while (ugen.next_dag(g)) {
            synth.reset(nrin, g.nr_vertices());
            auto result = synth.synthesize(tt, g, c1);
            if (result == success) {
                break;
            }
        }

        igen.reset(nrin);
        while (igen.next_dag(g)) {
            assert(g.nr_vertices() <= c1.nr_steps());
            synth.reset(nrin, g.nr_vertices());
            auto result = synth.perm_synthesize(tt, g, c2, perm);
            if (result == success) {
                break;
            }
        }

        auto c1_nr_steps = c1.nr_steps();
        auto c2_nr_steps = c2.nr_steps();
        auto sim_tts1 = c1.simulate();
        auto sim_tts2 = c2.simulate();
        assert(c1_nr_steps == c2_nr_steps);
        assert(*sim_tts1[0] == *sim_tts2[0]);
    } 
}

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
    auto npn_set = get_npn_classes<nrin>();

    dag g;
    vector<int> perm(nrin);
    chain<static_truth_table<nrin>> c1;
    chain<static_truth_table<nrin>> c2;
    unbounded_dag_generator<sat_solver*> ugen;
    nonisomorphic_dag_generator<sat_solver*> igen;
    dag_synthesizer<static_truth_table<nrin>,sat_solver*> synth;

    int i = 0;
    for (auto& npn_tt : npn_set) {
        printf("i = %d\n", ++i);
        static_truth_table<nrin> tt = npn_tt;

        // We skip the trivial functions
        if (is_trivial(tt)) {
            continue;
        }
        
        ugen.reset(nrin);
        while (ugen.next_dag(g)) {
            synth.reset(nrin, g.nr_vertices());
            auto result = synth.synthesize(tt, g, c1);
            if (result == success) {
                break;
            }
        }

        igen.reset(nrin);
        while (igen.next_dag(g)) {
            synth.reset(nrin, g.nr_vertices());
            auto result = synth.perm_synthesize(tt, g, c2, perm);
            if (result == success) {
                break;
            }
        }

        auto c1_nr_steps = c1.nr_steps();
        auto c2_nr_steps = c2.nr_steps();
        auto sim_tts1 = c1.simulate();
        auto sim_tts2 = c2.simulate();
        assert(c1_nr_steps == c2_nr_steps);
        assert(*sim_tts1[0] == *sim_tts2[0]);
    }
}

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
    check_equivalence<5>(full_coverage);

    check_npn_equivalence<4>();

    return 0;
}

