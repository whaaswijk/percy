#include <percy/percy.hpp>
#include <cassert>
#include <cstdio>
#include <ctime>

using namespace percy;

/*******************************************************************************
    Times fence generators and filters. Here to ensure that this phase of
    synthesis is sufficiently fast.
*******************************************************************************/
int main(void)
{
    // Upper bound on the amount of time (ms) fence generation may take
    const auto upper_bound = 0.05;


    // Time unfiltered fence generation
    auto start = clock();
    fence f;
    for (unsigned k = 1; k <= 5; k++) {
        for (unsigned l = 1; l <= k; l++) {
            partition_generator g(k, l);
            while (g.next_fence(f)) { }
        }
    }
    auto stop = clock();
    double elapsedms = (double)(stop - start) * 1000.0 / CLOCKS_PER_SEC;
    printf("elapsedms=%f\n", elapsedms);
    assert(elapsedms < upper_bound);

    // Time PO based filtering 
    start = clock();
    for (unsigned k = 1; k <= 5; k++) {
        for (unsigned l = 1; l <= k; l++) {
            po_filter<partition_generator> g(partition_generator(k, l), 1, 2);
            while (g.next_fence(f)) { }
        }
    }
    stop = clock();
    elapsedms = (double)(stop - start) * 1000.0 / CLOCKS_PER_SEC;
    printf("elapsedms=%f\n", elapsedms);
    assert(elapsedms < upper_bound);

    return 0;
}

