#pragma once

#include "solver_wrapper.hpp"

#define STRINGIFY(s) XSTRINGIFY(s)
#define XSTRINGIFY(s) #s

#define testingnur 3
#pragma message ("abc = " STRINGIFY(abc))
#pragma message ("pabc = " STRINGIFY(pabc))
#pragma message ("ABC_NAMESPACE = " STRINGIFY(ABC_NAMESPACE))
#pragma message ("testingnur = " STRINGIFY(testingnur))

namespace percy
{
    class bsat_wrapper : public solver_wrapper
    {
    private:
        pabc::sat_solver * solver = NULL;

    public:
        bsat_wrapper()
        {
            solver = pabc::sat_solver_new();
        }

        ~bsat_wrapper()
        {
            pabc::sat_solver_delete(solver);
            solver = NULL;
        }

        void restart()
        {
            pabc::sat_solver_restart(solver);
        }

        void set_nr_vars(int nr_vars)
        {
            pabc::sat_solver_setnvars(solver, nr_vars);
        }

        int nr_vars()
        {
            return pabc::sat_solver_nvars(solver);
        }

        int nr_clauses()
        {
            return pabc::sat_solver_nclauses(solver);
        }

        int nr_conflicts()
        {
            return pabc::sat_solver_nconflicts(solver);
        }

        int add_clause(lit* begin, lit* end)
        {
            return pabc::sat_solver_addclause(solver, begin, end);
        }

        void add_var()
        {
            pabc::sat_solver_addvar(solver);
        }

        int var_value(int var)
        {
            return pabc::sat_solver_var_value(solver, var);
        }

        synth_result solve(int cl)
        {
            auto res = pabc::sat_solver_solve(solver, 0, 0, cl, 0, 0, 0);
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
            auto res = pabc::sat_solver_solve(solver, begin, end, cl, 0, 0, 0);
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
