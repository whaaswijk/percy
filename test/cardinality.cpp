#include <percy/sat_circuits.hpp>
#include <cstdio>
#include <fstream>
#include <iostream>
#include <vector>
#include <percy/misc.hpp>

#define MAX_SUM_VARS 256

using namespace percy;
using std::vector;

int
block_solution(sat_solver* s, vector<int> sum_vars)
{
    int lits[MAX_SUM_VARS];

    for (int i = 0; i < sum_vars.size(); i++) {
        const auto sum_var = sum_vars[i];
        lits[i] = abc::Abc_Var2Lit(sum_var, solver_var_value(s, sum_var));
    }
    return solver_add_clause(s, lits, lits + sum_vars.size());
}

void
enumerate_solutions(int nr_svars, int C)
{
    assert(nr_svars <= MAX_SUM_VARS);
    sat_solver* s;
    solver_alloc(&s);

    vector<int> sum_vars;
    vector<int> res_vars;

    int nr_res_vars = (C + 2) * (nr_svars + 1);
    printf("C = %d\n", C);
    printf("nr_svars = %d\n", nr_svars);
    printf("nr_res_vars = %d\n", nr_res_vars);
    solver_set_nr_vars(s, nr_svars + nr_res_vars);

    for (int i = 0; i < nr_svars; i++) {
        sum_vars.push_back(i);
    }
    for (int i = 0; i < nr_res_vars; i++) {
        res_vars.push_back(nr_svars + i);
    }
    create_cardinality_circuit(s, sum_vars, res_vars, C);

    int nr_valid_cardinality_solutions = 0;
    while (true) {
        auto status = solver_solve(s);
        if (status != success) {
            break;
        }
        for (int i = 0; i < nr_svars; i++) {
            printf("s_%d ", i);
        }
        printf("\n");
        for (int i = 0; i < nr_svars; i++) {
            printf("  %d ", solver_var_value(s, i));
        }
        printf("\n");

        for (int i = 0; i < nr_svars + 1; i++) {
            for (int j = 0; j < C + 2; j++) {
                printf("res_%d[%d] ", i, j);
            }
            printf("\n");
            for (int j = 0; j < C + 2; j++) {
                printf("   %d    ", solver_var_value(s, nr_svars + i * (C + 2) + j));
            }
            printf("\n");

            if (i == nr_svars && solver_var_value(s, nr_svars + i * (C + 2) + C)) {
                ++nr_valid_cardinality_solutions;
            }
        }
        printf("\n");
        auto res = block_solution(s, sum_vars);
        if (!res) {
            break;
        }
    }

    solver_dealloc(&s);

    // Verify that the number of solutions where res[C] == 1 is (sum_vars.size() choose C)
    assert(nr_valid_cardinality_solutions == binomial_coeff(sum_vars.size(), C));
}

/// Tests the creation of cardinality constraint circuits in SAT solvers.
int main(void)
{
    enumerate_solutions(2, 2);
    enumerate_solutions(4, 2);
    enumerate_solutions(4, 3);
    
    return 0;
}

