#include <topsynth/topsynth.hpp>
#include <cstdio>
#include <fstream>

using namespace topsynth;

/*******************************************************************************
    Verifies that the DAG to .dot conversion works properly.
*******************************************************************************/
int main(void)
{
    int ctr = 0;
    dag g;
    unbounded_dag_generator<sat_solver*> ugen;

    ugen.reset(3);
    ctr = 0;
    while (ugen.next_dag(g)) {
        if (++ctr > 10) {
            break;
        }
        g.to_dot(std::cout);
    }

    ugen.reset(4);
    ctr = 0;
    while (ugen.next_dag(g)) {
        if (++ctr > 10) {
            break;
        }
        g.to_dot(std::cout);
    }

    return 0;
}

