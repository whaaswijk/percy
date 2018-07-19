#include <percy/percy.hpp>
#include <ctime>

using namespace percy;

int main(void)
{
    auto dags = pd_generate_max(7);
    auto dags_filtered = pd_generate_filtered(7, 4);

    printf("found %lu DAGs\n", dags.size());
    printf("found %lu filtered DAGs\n", dags_filtered.size());

    const auto nr_iso_vertices = 7;
    dags = pd_generate(nr_iso_vertices);
    printf("nr dags with %d vertices: %zu\n", nr_iso_vertices, dags.size());

    std::vector<partial_dag> ni_dags;
    auto start = std::clock();
    pd_filter_isomorphic(dags, ni_dags);
    const auto elapsed1 = std::clock() - start;
    const auto nr_ni1 = ni_dags.size();

    ni_dags.clear();
    start = std::clock();
    pd_filter_isomorphic_fast(dags, ni_dags);
    const auto elapsed2 = std::clock() - start;
    const auto nr_ni2 = ni_dags.size();

    assert(nr_ni1 == nr_ni2);
    printf("nr non iso: %zu\n", ni_dags.size());
    printf("elapsed1 = %.2fms\n", (1000.0 * elapsed1) / CLOCKS_PER_SEC);
    printf("elapsed2 = %.2fms\n", (1000.0 * elapsed2) / CLOCKS_PER_SEC);

    return 0;
}
