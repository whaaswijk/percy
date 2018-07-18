#include <percy/percy.hpp>

using namespace percy;

int main(void)
{
    auto dags = pd_generate_max(7);
    auto dags_filtered = pd_generate_filtered(7, 4);

    printf("found %lu DAGs\n", dags.size());
    printf("found %lu filtered DAGs\n", dags_filtered.size());

    return 0;
}