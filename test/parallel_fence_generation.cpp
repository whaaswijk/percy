#include <topsynth/topsynth.hpp>
#include <cassert>
#include <cstdio>

using namespace topsynth;
using std::vector;

/*******************************************************************************
    Verifies that fence generation using a concurrent queue works the same as
    sequential generation.
*******************************************************************************/
int main(void)
{
    fence f;
    vector<fence> v;
    moodycamel::ConcurrentQueue<fence> q(2048);

    for (int k = 1; k <= 12; k++) {
        auto v = generate_fences(k);
        generate_fences(k, q);
        auto qfences = 0;
        while (q.try_dequeue(f)) {
            ++qfences;
        }
        assert(qfences == v.size());
        printf("# fences = %d\n", qfences);
    }
}

