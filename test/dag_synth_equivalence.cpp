#include <percy/percy.hpp>
#include <percy/io.hpp>

#define MAX_TESTS 256

using namespace percy;
using kitty::static_truth_table;


template<int nr_in>
void gen_check_equivalence(bool full_coverage)
{
    dag<2> g;
    unbounded_dag_generator<sat_solver*> ugen;

    auto synth1 = new_std_synth();
    auto synth2 = new_dag_synth();

    synth_spec<static_truth_table<nr_in>> spec(nr_in, 1);
    spec.add_nontriv_clauses = true;
    spec.add_alonce_clauses = true;
    spec.add_noreapply_clauses = true;
    spec.add_colex_clauses = true;
    spec.add_colex_func_clauses = true;
    spec.add_symvar_clauses = true;

    spec.verbosity = 0;


    // don't run too many tests.
    auto max_tests = (1 << (1 << nr_in));
    if (!full_coverage) {
        max_tests = std::min(max_tests, MAX_TESTS);
    }
    static_truth_table<nr_in> tt;

    chain<2> c1;
    chain<2> c2;

    for (auto i = 1; i < max_tests; i++) {
        kitty::create_from_words(tt, &i, &i+1);

        // We skip the trivial functions
        if (is_trivial(tt)) {
            continue;
        }
        spec.functions[0] = &tt;
        auto res1 = synth1->synthesize(spec, c1);
        assert(res1 == success);
        auto sim_tts1 = c1.template simulate<static_truth_table<nr_in>>();
        auto c1_nr_steps = c1.get_nr_vertices();

        const auto dag_found = find_dag(spec, g, nr_in);
        assert(dag_found == success);
        auto result = synth2->synthesize(spec, g, c2);
        assert(result == success);
        auto c2_nr_steps = c2.get_nr_vertices();
        auto sim_tts2 = c2.template simulate<static_truth_table<nr_in>>();
        assert(c1_nr_steps == c2_nr_steps);
        assert(sim_tts1[0] == sim_tts2[0]);

        printf("(%d/%d)\r", i + 1, max_tests);
        fflush(stdout);
    }
    printf("\n");
}

template<int nr_in>
void check_equivalence(bool full_coverage)
{
    dag<2> g;
    unbounded_dag_generator<sat_solver*> ugen;

    auto synth1 = new_std_synth();
    auto synth2 = new_dag_synth();
       
    synth_spec<static_truth_table<nr_in>> spec(nr_in, 1);
    spec.add_nontriv_clauses = true;
    spec.add_alonce_clauses = true;
    spec.add_noreapply_clauses = true;
    spec.add_colex_clauses = true;
    spec.add_colex_func_clauses = true;
    spec.add_symvar_clauses = true;

    spec.verbosity = 0;

    // don't run too many tests.
    auto max_tests = (1 << (1 << nr_in));
    if (!full_coverage) {
        max_tests = std::min(max_tests, MAX_TESTS);
    }
    static_truth_table<nr_in> tt;

    chain<2> c1;
    chain<2> c2;

    for (auto i = 1; i < max_tests; i++) {
        kitty::create_from_words(tt, &i, &i+1);

        // We skip the trivial functions
        if (is_trivial(tt)) {
            continue;
        }
        spec.functions[0] = &tt;

        auto res1 = synth1->synthesize(spec, c1);
        assert(res1 == success);
        auto sim_tts1 = c1.template simulate<static_truth_table<nr_in>>();
        auto c1_nr_steps = c1.get_nr_vertices();

        ugen.reset(nr_in);
        int min_size = -1;
        while (ugen.next_dag(g)) {
            if (min_size != -1 && g.get_nr_vertices() > min_size) {
                break;
            }
            auto result = synth2->synthesize(spec, g, c2);
            if (result == success) {
                auto c2_nr_steps = c2.get_nr_vertices();
                if (min_size == -1) {
                    min_size = c2_nr_steps;
                }
                auto sim_tts2 = 
                    c2.template simulate<static_truth_table<nr_in>>();
                assert(c1_nr_steps == c2_nr_steps);
                assert(sim_tts1[0] == sim_tts2[0]);
            } else {
                assert(result == failure);
            }
        }
        printf("(%d/%d)\r", i + 1, max_tests);
        fflush(stdout);
    }
    printf("\n");
}

template<int nr_in>
auto
get_npn_classes()
{
    std::unordered_set<static_truth_table<nr_in>, kitty::hash<static_truth_table<nr_in>>> classes;
    static_truth_table<1 << nr_in> map;
    std::transform(map.cbegin(), map.cend(), map.begin(), 
            []( auto w ) { return ~w; } );

    int64_t index = 0;
    static_truth_table<nr_in> tt;
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

template<int nr_in>
void check_npn_equivalence()
{
    auto npn_set = get_npn_classes<nr_in>();

    dag<2> g;
    unbounded_dag_generator<sat_solver*> ugen;

    auto synth1 = new_std_synth();
    auto synth2 = new_dag_synth();

    synth_spec<static_truth_table<nr_in>> spec(nr_in, 1);
    spec.add_nontriv_clauses = true;
    spec.add_alonce_clauses = true;
    spec.add_noreapply_clauses = true;
    spec.add_colex_clauses = true;
    spec.add_colex_func_clauses = true;
    spec.add_symvar_clauses = true;

    spec.verbosity = 0;

    chain<2> c1;
    chain<2> c2;

    int i = 0;
    for (auto& npn_tt : npn_set) {
        static_truth_table<nr_in> tt = npn_tt;

        // We skip the trivial functions
        if (is_trivial(tt)) {
            continue;
        }
        auto support = min_base_inplace(tt);
        if (support.size() < nr_in) {
            continue;
        }
        expand_inplace(tt, support);

        spec.functions[0] = &tt;
        auto res1 = synth1->synthesize(spec, c1);
        assert(res1 == success);
        auto sim_tts1 = c1.template simulate<static_truth_table<nr_in>>();
        auto c1_nr_steps = c1.get_nr_vertices();

        ugen.reset(nr_in);
        int min_size = -1;
        while (ugen.next_dag(g)) {
            if (min_size != -1 && g.get_nr_vertices() > min_size) {
                break;
            }
            auto result = synth2->synthesize(spec, g, c2);
            if (result == success) {
                auto c2_nr_steps = c2.get_nr_vertices();
                if (min_size == -1) {
                    min_size = c2_nr_steps;
                }
                auto sim_tts2 = 
                    c2.template simulate<static_truth_table<nr_in>>();
                assert(c1_nr_steps == c2_nr_steps);
                assert(sim_tts1[0] == sim_tts2[0]);
            }
        }
        const auto dag_found = find_dag(spec, g, nr_in);
        assert(dag_found == success);
        auto result = synth2->synthesize(spec, g, c2);
        assert(result == success);
        auto c2_nr_steps = c2.get_nr_vertices();
        auto sim_tts2 = c2.template simulate<static_truth_table<nr_in>>();
        assert(c1_nr_steps == c2_nr_steps);
        assert(sim_tts1[0] == sim_tts2[0]);
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

    if (full_coverage) {
        check_npn_equivalence<4>();
    }

    return 0;
}

