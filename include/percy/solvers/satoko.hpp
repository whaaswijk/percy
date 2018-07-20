#pragma once

#ifndef DISABLE_SATOKO

#include "solver_wrapper.hpp"

#pragma GCC diagnostic push

#pragma GCC diagnostic ignored "-Wtype-limits"
#include <satoko/satoko.h>
#pragma GCC diagnostic pop

namespace percy
{
    class satoko_wrapper : public solver_wrapper
    {
    private:
        pabc::satoko_t * solver = NULL;

    public:
        satoko_wrapper()
        {
            solver = pabc::satoko_create();
        }

        ~satoko_wrapper()
        {
            pabc::satoko_destroy(solver);
            solver = NULL;
        }

        void restart()
        {
            pabc::satoko_reset(solver);
        }

        void set_nr_vars(int nr_vars)
        {
            pabc::satoko_setnvars(solver, nr_vars);
        }

        int nr_vars()
        {
            return pabc::satoko_varnum(solver);
        }

        int nr_clauses()
        {
            return pabc::satoko_clausenum(solver);
        }

        int nr_conflicts()
        {
            return pabc::satoko_conflictnum(solver);
        }

        int add_clause(pabc::lit* begin, pabc::lit* end)
        {
            return pabc::satoko_add_clause(solver, begin, end - begin);
        }

        void add_var()
        {
            pabc::satoko_add_variable(solver, 0);
        }

        int var_value(int var)
        {
            return pabc::satoko_read_cex_varvalue(solver, var);
        }

        synth_result solve(int cl)
        {
            auto res = pabc::satoko_solve_assumptions_limit(solver, 0, 0, cl);
            if (res == pabc::SATOKO_SAT) {
                return success;
            } else if (res == pabc::SATOKO_UNSAT) {
                return failure;
            } else {
                return timeout;
            }
        }

        synth_result solve(pabc::lit* begin, pabc::lit* end, int cl)
        {
            auto res = pabc::satoko_solve_assumptions_limit(solver, begin, end - begin, cl);
            if (res == pabc::SATOKO_SAT) {
                return success;
            } else if (res == pabc::SATOKO_UNSAT) {
                return failure;
            } else {
                return timeout;
            }
        }

    };
}

#endif // !DISABLE_SATOKO
