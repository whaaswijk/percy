#pragma once

#include "solver_wrapper.hpp"

namespace percy
{
    class bsat_wrapper : public solver_wrapper
    {
    private:
        sat_solver * solver = NULL;

    public:
        bsat_wrapper()
        {
            solver = abc::sat_solver_new();
        }

        ~bsat_wrapper()
        {
            sat_solver_delete(solver);
            solver = NULL;
        }

        void restart()
        {
            sat_solver_restart(solver);
        }

        void set_nr_vars(int nr_vars)
        {
            sat_solver_setnvars(solver, nr_vars);
        }

        int nr_vars()
        {
            return sat_solver_nvars(solver);
        }

        int nr_clauses()
        {
            return sat_solver_nclauses(solver);
        }

        int nr_conflicts()
        {
            return sat_solver_nconflicts(solver);
        }

        int add_clause(lit* begin, lit* end)
        {
            return sat_solver_addclause(solver, begin, end);
        }

        void add_var()
        {
            sat_solver_addvar(solver);
        }

        int var_value(int var)
        {
            return sat_solver_var_value(solver, var);
        }

        synth_result solve(int cl)
        {
            auto res = sat_solver_solve(solver, 0, 0, cl, 0, 0, 0);
            if (res == 1) {
                return success;
            } else if (res == -1) {
                return failure;
            } else {
                return timeout;
            }
        }

        synth_result solve(lit* begin, lit* end, int cl)
        {
            auto res = sat_solver_solve(solver, begin, end, cl, 0, 0, 0);
            if (res == 1) {
                return success;
            } else if (res == -1) {
                return failure;
            } else {
                return timeout;
            }
        }

    };
}