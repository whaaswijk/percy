#pragma once

#if !defined(_WIN32) && !defined(_WIN64)

#ifdef USE_SYRUP
#include <syrup/parallel/MultiSolvers.h>
#define SolverType Glucose::MultiSolvers
#else
#include <glucose/core/Solver.h>
#define SolverType Glucose::Solver
#endif

namespace percy
{

    class glucose_wrapper : public solver_wrapper
    {
    private:
        
    public:
        glucose_wrapper()
        {
            solver = new SolverType;
        }

        ~glucose_wrapper()
        {
            delete solver;
            solver = NULL;
        }

        void restart()
        {
            delete solver;
            solver = new SolverType;
        }


        void set_nr_vars(int nr_vars)
        {
            while (nr_vars-- > 0) {
                solver->newVar();
            }
        }

        int nr_vars()
        {
            return s->nVars();
        }

        int nr_clauses()
        {
            return solver->nClauses();
        }

        int nr_conflicts()
        {
#ifdef USE_SYRUP
            return s->conflicts;
#else
            // Currently not supported by Glucose::MultiSolvers
            return 0;
#endif
        }

        int add_clause(lit* begin, lit* end)
        {
            Glucose::vec<Glucose::Lit> litvec;
            for (auto i = begin; i != end; i++) {
                litvec.push(Glucose::mkLit((*i >> 1), (*i & 1)));
            }
            return solver->addClause(litvec);
        }

        void add_var()
        {
            solver->newVar();
        }

        int var_value(int var)
        {
            return solver->modelValue(var) == l_True;
        }

        synth_result solve(int cl)
        {
#ifndef USE_SYRUP
            Glucose::vec<Glucose::Lit> litvec;
            if (cl) {
                solver->setConfBudget(cl);
            }
            auto res = solver->solveLimited(litvec);
            if (res == l_True) {
                return success;
            } else if (res == l_False) {
                return failure;
            } else {
                return timeout;
            }
#else
            int ret2 = solver->simplify();
            solver->use_simplification = false;
            if (ret2) {
                solver->eliminate();
            }

            if (!ret2 || !solver->okay()) {
                return failure;
            }

            // Conflict limits are currently not supported by 
            // Glucose::MultiSolvers.   
            auto res = solver->solve();
            if (res == l_True) {
                return success;
            } else if (res == l_False) {
                return failure;
            } else {
                return timeout;
            }
#endif
        }


        synth_result solve(lit* begin, lit* end, int cl)
        {
#ifndef USE_SYRUP
            Glucose::vec<Glucose::Lit> litvec;
            for (auto i = begin; i != end; i++) {
                litvec.push(Glucose::mkLit((*i >> 1), (*i & 1)));
            }
            if (cl) {
                solver->setConfBudget(cl);
            }
            auto res = solver->solveLimited(litvec);
            if (res == l_True) {
                return success;
            } else if (res == l_False) {
                return failure;
            } else {
                return timeout;
            }
#else
            return solve(s, cl);
        }
#endif
    };
}

#endif