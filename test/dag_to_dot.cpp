#include <percy/percy.hpp>
#include <percy/io.hpp>
#include <cstdio>
#include <fstream>

using namespace percy;

/*******************************************************************************
    Verifies that the DAG to .dot conversion works properly.
*******************************************************************************/
int main(void)
{
    int ctr = 0;
    binary_dag g;
    unbounded_dag_generator<sat_solver*> ugen;

    ugen.reset(3);
    ctr = 0;
    while (ugen.next_dag(g)) {
        if (++ctr > 10) {
            break;
        }
        to_dot(g, std::cout);
    }

    ugen.reset(4);
    ctr = 0;
    while (ugen.next_dag(g)) {
        if (++ctr > 10) {
            break;
        }
        to_dot(g, std::cout);
    }

    ternary_dag h(5, 4);
    h.set_vertex(0, { 0, 1, 2});
    h.set_vertex(1, { 4, 3, 1});
    h.set_vertex(2, { 5, 6, 0});
    h.set_vertex(3, { 7, 6, 1});
    to_dot(h, std::cout);

    return 0;
}

