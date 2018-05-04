#pragma once

#include <base/abc/abc.h>
#include <misc/vec/vecInt.h>
#include <misc/vec/vecPtr.h>
#include <sat/bsat/satSolver.h>
#include <thread>

#ifdef USE_SYRUP
#include <syrup/parallel/MultiSolvers.h>
#else
#include <glucose/core/Solver.h>
#endif

using abc::lit;
using abc::sat_solver;

namespace percy 
{
    enum synth_result
    {
        success,
        failure,
        timeout
    };

	template<typename S>
	void solver_alloc(S*);
	
    template<typename S>
	void solver_dealloc(S*);

	template<typename S>
	void solver_restart(S*);

	template<typename S>
	void solver_set_nr_vars(S, unsigned nr_vars);
	
    template<typename S>
	int solver_nr_vars(S);
    
    template<typename S>
	int solver_nr_clauses(S);
    
    template<typename S>
    int solver_nr_conflicts(S);
	
    template<typename S>
	void solver_add_var(S);

	template<typename S>
	int solver_add_clause(S, lit* begin, lit* end);

	template<typename S>
	synth_result solver_solve(S, int conflict_limit=0);
	
    template<typename S>
	synth_result solver_solve(S, lit* begin, lit* end, int conflict_limit=0);

	template<typename S>
	int solver_var_value(S, int var);


	template<>
	inline void solver_alloc<sat_solver*>(sat_solver** s) 
    {
		*s = abc::sat_solver_new();
	}

	template<>
	inline void solver_dealloc<sat_solver*>(sat_solver** s)
    {
		sat_solver_delete(*s);
		*s = NULL;
	}

	template<>
	inline void solver_restart<sat_solver*>(sat_solver** s) 
    {
		sat_solver_restart(*s);
	}

	template<>
	inline void 
    solver_set_nr_vars<sat_solver*>(sat_solver* s, unsigned nr_vars) 
    {
		sat_solver_setnvars(s, nr_vars);
	}

    template<>
    inline int
	solver_nr_vars(sat_solver* s)
    {
        return sat_solver_nvars(s);
    }
    
    template<>
	inline int 
    solver_nr_clauses(sat_solver* s)
    {
        return sat_solver_nclauses(s);
    }

    template<>
	inline int 
    solver_nr_conflicts(sat_solver* s)
    {
        return sat_solver_nconflicts(s);
    }

	template<>
	inline int 
    solver_add_clause<sat_solver*>(sat_solver* s, lit* begin, lit* end) 
    {
		return sat_solver_addclause(s, begin, end);
	}

    template<>
	inline void 
    solver_add_var<sat_solver*>(sat_solver* s)
    {
		sat_solver_addvar(s);
	}

	template<>
	inline int solver_var_value<sat_solver*>(sat_solver* s, int var) 
    {
		return sat_solver_var_value(s, var);
	}

    template<>
	inline synth_result 
    solver_solve<sat_solver*>(sat_solver* s, int cl) 
    {
		auto res = sat_solver_solve(s, 0, 0, cl, 0, 0, 0);
        if (res == 1) {
            return success;
        } else if (res == -1) {
            return failure;
        } else {
            return timeout;
        }
	}

	template<>
	inline synth_result 
    solver_solve<sat_solver*>(sat_solver* s, lit* begin, lit* end, int cl) 
    {
		auto res = sat_solver_solve(s, begin, end, cl, 0, 0, 0);
        if (res == 1) {
            return success;
        } else if (res == -1) {
            return failure;
        } else {
            return timeout;
        }
	}

#ifndef USE_SYRUP
    template<>
	inline void solver_alloc(Glucose::Solver** s) 
    {
		*s = new Glucose::Solver();
	}

	template<>
	inline void solver_dealloc(Glucose::Solver** s)
    {
        delete *s;
        *s = nullptr;
	}

	template<>
	inline void solver_restart(Glucose::Solver** s) 
    {
		delete *s;
        *s = new Glucose::Solver();
	}

	template<>
	inline void 
    solver_set_nr_vars(Glucose::Solver* s, unsigned nr_vars) 
    {
        while (nr_vars-- > 0) {
            s->newVar();
        }
	}

    template<>
    inline int
	solver_nr_vars(Glucose::Solver* s)
    {
        return s->nVars();
    }
    
    template<>
	inline int 
    solver_nr_clauses(Glucose::Solver* s)
    {
        return s->nClauses();
    }

    template<>
        inline int 
    solver_nr_conflicts(Glucose::Solver* s)
    {
        return s->conflicts;
    }

	template<>
	inline int 
    solver_add_clause(Glucose::Solver* s, lit* begin, lit* end) 
    {
        Glucose::vec<Glucose::Lit> litvec;
        for (auto i = begin; i != end; i++) {
            litvec.push(Glucose::mkLit((*i >> 1), (*i & 1)));
        }
		return s->addClause_(litvec);
	}

    template<>
	inline void 
    solver_add_var(Glucose::Solver* s)
    {
		s->newVar();
	}

	template<>
	inline int solver_var_value(Glucose::Solver* s, int var) 
    {
		return s->modelValue(var) == l_True;
	}

    template<>
	inline synth_result 
    solver_solve(Glucose::Solver* s, int cl) 
    {
        Glucose::vec<Glucose::Lit> litvec;
        if (cl) {
            s->setConfBudget(cl);
        }
		auto res = s->solveLimited(litvec);
        if (res == l_True) {
            return success;
        } else if (res == l_False) {
            return failure;
        } else {
            return timeout;
        }
	}

	template<>
	inline synth_result 
    solver_solve(Glucose::Solver* s, lit* begin, lit* end, int cl) 
    {
        Glucose::vec<Glucose::Lit> litvec;
        for (auto i = begin; i != end; i++) {
            litvec.push(Glucose::mkLit((*i >> 1), (*i & 1)));
        }
        if (cl) {
            s->setConfBudget(cl);
        }
		auto res = s->solveLimited(litvec);
        if (res == l_True) {
            return success;
        } else if (res == l_False) {
            return failure;
        } else {
            return timeout;
        }
	}
#else
    template<>
	inline void solver_alloc(Glucose::MultiSolvers** s) 
    {
        //auto nr_threads = 2;
        //*s = new Glucose::MultiSolvers(nr_threads);
        *s = new Glucose::MultiSolvers();
	}

	template<>
	inline void solver_dealloc(Glucose::MultiSolvers** s)
    {
        delete *s;
        *s = nullptr;
	}

	template<>
	inline void solver_restart(Glucose::MultiSolvers** s) 
    {
        delete *s;
        //auto nr_threads = 2;
        //*s = new Glucose::MultiSolvers(nr_threads);
        *s = new Glucose::MultiSolvers();
	}

	template<>
	inline void 
    solver_set_nr_vars(Glucose::MultiSolvers* s, unsigned nr_vars) 
    {
        while (nr_vars-- > 0) {
            s->newVar();
        }
	}

    template<>
    inline int
	solver_nr_vars(Glucose::MultiSolvers* s)
    {
        return s->nVars();
    }
    
    template<>
	inline int 
    solver_nr_clauses(Glucose::MultiSolvers* s)
    {
        return s->nClauses();
    }

    template<>
        inline int 
    solver_nr_conflicts(Glucose::MultiSolvers* s)
    {
        // Currently not supported by Glucose::MultiSolvers.
        return 0;
    }

	template<>
	inline int 
    solver_add_clause(Glucose::MultiSolvers* s, lit* begin, lit* end) 
    {
        Glucose::vec<Glucose::Lit> litvec;
        for (auto i = begin; i != end; i++) {
            litvec.push(Glucose::mkLit((*i >> 1), (*i & 1)));
        }
        return s->addClause(litvec);
	}

    template<>
	inline void 
    solver_add_var(Glucose::MultiSolvers* s)
    {
        s->newVar();
	}

	template<>
	inline int solver_var_value(Glucose::MultiSolvers* s, int var) 
    {
        return s->model[var] == l_True;
	}

    template<>
	inline synth_result 
    solver_solve(Glucose::MultiSolvers* s, int cl) 
    {
        int ret2 = s->simplify();   
        s->use_simplification = false;
        if(ret2) {
            s->eliminate();
        }

        if (!ret2 || !s->okay()){
            return failure;
        }

        // Conflict limits are currently not supported by Glucose::MultiSolvers.   
        auto res = s->solve();
        if (res == l_True) {
            return success;
        } else if (res == l_False) {
            return failure;
        } else {
            return timeout;
        }
	}

	template<>
	inline synth_result 
    solver_solve(Glucose::MultiSolvers* s, lit* begin, lit* end, int cl) 
    {
        return solver_solve(s, cl);
	}
#endif

}

