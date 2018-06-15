#pragma once

#include <abc/satSolver.h>
#include <thread>

namespace percy
{
    using abc::lit;
	using abc::sat_solver;
	using abc::Abc_LitIsCompl;
	using abc::Abc_Lit2Var;

    enum synth_result
    {
        success,
        failure,
        timeout
    };

    class solver_wrapper
    {
    public:
        virtual ~solver_wrapper() ///< Virtual constructor allows for cleanup in derived class destructors
        {

        }
        virtual void restart() = 0;
        virtual void set_nr_vars(int nr_vars) = 0;
        virtual int  nr_vars() = 0;
        virtual int  nr_clauses() = 0;
        virtual int  nr_conflicts() = 0;
        virtual void add_var() = 0;
        virtual int  add_clause(lit* begin, lit* end) = 0;
        virtual int  var_value(int var) = 0;
        virtual synth_result solve(int conflict_limit = 0) = 0;
        virtual synth_result solve(lit* begin, lit* end, int conflict_limit = 0) = 0;
    };
	
}