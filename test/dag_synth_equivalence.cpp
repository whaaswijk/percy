#include <topsynth/topsynth.hpp>

#define MAX_TESTS 512

using namespace topsynth;
using kitty::static_truth_table;


template<int nrin>
void gen_check_equivalence(bool full_coverage)
{
    dag g;
    unbounded_dag_generator<sat_solver*> ugen;

    synth_spec<static_truth_table<nrin>,sat_solver*> spec;
    simple_synthesizer<static_truth_table<nrin>,sat_solver*,2> synth1;
    dag_synthesizer<static_truth_table<nrin>,sat_solver*> synth2;

    spec.nr_in = nrin;
    spec.nr_out = 1;
    spec.verbosity = 0;

    // don't run too many tests.
    auto max_tests = (1 << (1 << nrin));
    if (!full_coverage) {
        max_tests = std::min(max_tests, MAX_TESTS);
    }
    static_truth_table<nrin> tt;

    chain<static_truth_table<nrin>> c1;
    chain<static_truth_table<nrin>> c2;

    for (auto i = 1; i < max_tests; i++) {
        kitty::create_from_words(tt, &i, &i+1);

        // We skip the trivial functions
        if (is_trivial(tt)) {
            continue;
        }
        spec.functions[0] = &tt;
        auto res1 = synth1.synthesize(spec, c1);
        assert(res1 == success);
        auto sim_tts1 = c1.simulate();
        auto c1_nr_steps = c1.nr_steps();

        const auto dag_found = find_dag<static_truth_table<nrin>>(tt, g, nrin);
        assert(dag_found == success);
        synth2.reset(nrin, g.nr_vertices());
        auto result = synth2.synthesize(tt, g, c2);
        assert(result == success);
        auto c2_nr_steps = c2.nr_steps();
        auto sim_tts2 = c2.simulate();
        assert(c1_nr_steps == c2_nr_steps);
        assert(*sim_tts1[0] == *sim_tts2[0]);
    } 
}

template<int nrin>
void check_equivalence(bool full_coverage)
{
    dag g;
    unbounded_dag_generator<sat_solver*> ugen;

    synth_spec<static_truth_table<nrin>,sat_solver*> spec;
    simple_synthesizer<static_truth_table<nrin>,sat_solver*,2> synth1;
    dag_synthesizer<static_truth_table<nrin>,sat_solver*> synth2;

    spec.nr_in = nrin;
    spec.nr_out = 1;
    spec.verbosity = 0;

    // don't run too many tests.
    auto max_tests = (1 << (1 << nrin));
    if (!full_coverage) {
        max_tests = std::min(max_tests, MAX_TESTS);
    }
    static_truth_table<nrin> tt;

    chain<static_truth_table<nrin>> c1;
    chain<static_truth_table<nrin>> c2;

    for (auto i = 1; i < max_tests; i++) {
        kitty::create_from_words(tt, &i, &i+1);

        // We skip the trivial functions
        if (is_trivial(tt)) {
            continue;
        }
        spec.functions[0] = &tt;
        auto res1 = synth1.synthesize(spec, c1);
        assert(res1 == success);
        auto sim_tts1 = c1.simulate();
        auto c1_nr_steps = c1.nr_steps();

        ugen.reset(nrin);
        int min_size = -1;
        while (ugen.next_dag(g)) {
            if (min_size != -1 && g.nr_vertices() > min_size) {
                break;
            }
            synth2.reset(nrin, g.nr_vertices());
            auto result = synth2.synthesize(tt, g, c2);
            if (result == success) {
                auto c2_nr_steps = c2.nr_steps();
                if (min_size == -1) {
                    min_size = c2_nr_steps;
                }
                auto sim_tts2 = c2.simulate();
                assert(c1_nr_steps == c2_nr_steps);
                assert(*sim_tts1[0] == *sim_tts2[0]);
            }
        }
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
    unbounded_dag_generator<sat_solver*> ugen;

    synth_spec<static_truth_table<nrin>,sat_solver*> spec;
    colex_synthesizer<static_truth_table<nrin>,sat_solver*,2> synth1;
    dag_synthesizer<static_truth_table<nrin>,sat_solver*> synth2;

    spec.nr_in = nrin;
    spec.nr_out = 1;
    spec.verbosity = 0;

    chain<static_truth_table<nrin>> c1;
    chain<static_truth_table<nrin>> c2;

    int i = 0;
    for (auto& npn_tt : npn_set) {
        printf("i = %d\n", ++i);
        static_truth_table<nrin> tt = npn_tt;

        // We skip the trivial functions
        if (is_trivial(tt)) {
            continue;
        }
        auto support = min_base_inplace(tt);
        if (support.size() < nrin) {
            continue;
        }
        expand_inplace(tt, support);

        spec.functions[0] = &tt;
        auto res1 = synth1.synthesize(spec, c1);
        assert(res1 == success);
        auto sim_tts1 = c1.simulate();
        auto c1_nr_steps = c1.nr_steps();

        ugen.reset(nrin);
        int min_size = -1;
        while (ugen.next_dag(g)) {
            if (min_size != -1 && g.nr_vertices() > min_size) {
                break;
            }
            synth2.reset(nrin, g.nr_vertices());
            auto result = synth2.synthesize(tt, g, c2);
            if (result == success) {
                auto c2_nr_steps = c2.nr_steps();
                if (min_size == -1) {
                    min_size = c2_nr_steps;
                }
                auto sim_tts2 = c2.simulate();
                assert(c1_nr_steps == c2_nr_steps);
                assert(*sim_tts1[0] == *sim_tts2[0]);
            }
        }
        const auto dag_found = find_dag<static_truth_table<nrin>>(tt, g, nrin);
        assert(dag_found == success);
        synth2.reset(nrin, g.nr_vertices());
        auto result = synth2.synthesize(tt, g, c2);
        assert(result == success);
        auto c2_nr_steps = c2.nr_steps();
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
    
    gen_check_equivalence<2>(full_coverage);
    gen_check_equivalence<3>(full_coverage);

    check_npn_equivalence<4>();

    return 0;
}

