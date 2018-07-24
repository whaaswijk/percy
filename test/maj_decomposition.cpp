#include <percy/percy.hpp>
#include <cassert>
#include <cstdio>
#include <fstream>

using namespace percy;
using kitty::dynamic_truth_table;
using kitty::static_truth_table;

int main(void)
{
    const auto n = 6;
    const auto k = 3;
    spec spec;
    spec.verbosity = 0;

    chain c;

    static_truth_table<n> S_gt_k;
    create_threshold(S_gt_k, k);

    static_truth_table<n> S_eq_k;
    create_equals(S_eq_k, k);
    
    static_truth_table<n> S_par_k;
    static_truth_table<n> tmp;
    for (int i = 0; i < k; i++) {
        create_nth_var(tmp, i);
        S_par_k ^= tmp;
    }

    spec.nr_steps = 3;
    spec.fanin = 3;
    spec.add_primitive(MAJ);
    spec.compile_primitives();
    spec[0] = S_gt_k ^ (S_eq_k & S_par_k);
    spec.preprocess();

    cnf_formula cnf;
    knuth_encoder encoder(cnf);
    encoder.encode(spec);

    cnf.to_dimacs(stdout);

    return 0;
}

