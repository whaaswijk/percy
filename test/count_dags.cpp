#include <topsynth/topsynth.hpp>
#include <cstdio>
#include <fstream>

using namespace topsynth;

int main()
{
    // Count the number of 3/4-input DAGs with 3 to 7 nodes, for both true
    // and false DAGs.
    dag g;
    sat_dag_generator<sat_solver*> gen;

    for (int nr_vars = 3; nr_vars < 4; nr_vars++) {
        printf("n = %d\n", nr_vars);
        for (int nr_nodes = 1; nr_nodes < 7; nr_nodes++) {
            gen.gen_true_dags(true);
            gen.reset(nr_vars, nr_nodes);
            int nr_true_dags = 0;
            while (gen.next_dag(g)) {
                ++nr_true_dags;
            }
            gen.gen_true_dags(false);
            gen.reset(nr_vars, nr_nodes);
            int nr_false_dags = 0;
            while (gen.next_dag(g)) {
                ++nr_false_dags;
            }


            vector<dag> dags;
            int nr_non_isomorphic = 0;
            gen.gen_true_dags(false);
            gen.reset(nr_vars, nr_nodes);
            while (gen.next_dag(g)) {
                bool isomorphic = false;
                for (int i = dags.size() - 1; i >= 0; i--) {
                    auto g2 = dags[i];
                    if (g2.nr_vertices() != g.nr_vertices()) {
                        break;
                    }
                    if (g2.is_isomorphic(g)) {
                        isomorphic = true;
                        break;
                    }
                }
                if (!isomorphic) {
                    dags.push_back(g);
                    ++nr_non_isomorphic;
                }
            }

            printf("%d nodes: %d/%d/%d\n", nr_nodes, 
                    nr_non_isomorphic, nr_true_dags, nr_false_dags);
        }
    }

    rec_dag_generator rgen;
    for (int nr_vars = 3; nr_vars < 6; nr_vars++) {
        printf("n = %d\n", nr_vars);
        for (int nr_nodes = 1; nr_nodes < 8; nr_nodes++) {
            rgen.reset(nr_vars, nr_nodes);
            const auto nr_non_isomorphic = rgen.count_non_isomorphic_dags();
            rgen.reset(nr_vars, nr_nodes);
            const auto nr_dags = rgen.count_dags();
            printf("%d nodes: %d/%d\n", nr_nodes, 
                    nr_non_isomorphic, nr_dags);
        }
    }

    return 0;
}

