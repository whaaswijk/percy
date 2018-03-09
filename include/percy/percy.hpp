#pragma once

extern "C" 
{
    #include "base/abc/abc.h"
    #include "misc/vec/vecInt.h"
    #include "misc/vec/vecPtr.h"
    #include "sat/bsat/satSolver.h"
}

#include "fence.hpp"
#include "chain.hpp"
#include "sat_interface.hpp"
#include "dag_generation.hpp"
#include <memory>
#include <thread>
#include <mutex>
#include "tt_utils.hpp"
#include "concurrentqueue.h"
#include <chrono>

#define MAX_OUT 64 // The maximum supported number of outputs
#define MAX_STEPS 20 // The maximum number of steps we'll synthesize

using std::chrono::high_resolution_clock;
using std::chrono::duration;
using std::chrono::time_point;

/*******************************************************************************
    This module defines the interface to actually synthesize Boolean chains
    from specifications. The inspiration for this module is taken from Mathias
    Soeken's earlier exact synthesis algorithm, which has been integrated in
    the ABC synthesis package. That implementation is itself based on earlier
    work by Éen[1] and Knuth[2].

    [1] Niklas Éen, "Practical SAT – a tutorial on applied satisfiability
    solving," 2007, slides of invited talk at FMCAD.
    [2] Donald Ervin Knuth, "The Art of Computer Programming, Volume 4,
    Fascicle 6: Satisfiability," 2015
*******************************************************************************/
namespace percy
{
    template<typename TT, typename Solver>
    class synth_spec
    {
        public:
        int nr_in; // The number of inputs to the function 
        int tt_size; // The size of the truth table
        int op_size; // The size of the Boolean operators to synthesize
        int nr_out; // The number of outputs to synthesize
        int nr_steps; // The number of Boolean operators to use
        int nr_levels; // The number of levels in the Boolean fence
        int nr_op_vars; // Number of vars used to spec. operator functionality
        int nr_sel_vars; // Number of vars used to spec. operand selection
        int nr_out_vars; // Number of vars used to spec. output selection
        int nr_sim_vars; // Number of vars used to spec. global truth tables
        int sel_offset;
        int steps_offset;
        int out_offset;
        int sim_offset;
        int fence_offset;
        int verbosity; // Verbosity level for debugging purposes
        Solver _solver;
        uint64_t out_inv; // Is 1 at index i if output i must be inverted
        uint64_t triv_flag; // Is 1 at index i if output i is 0/1 or projection
        int nr_triv; // Number of trivial output functions
        int nr_nontriv; // Number of non-trivial output functions

        const TT* functions[MAX_OUT]; // The requested functions
        int triv_functions[MAX_OUT]; // Trivial outputs
        int synth_functions[MAX_OUT]; // Nontrivial outputs

        int selection_vars[MAX_STEPS][MAX_STEPS-2][MAX_STEPS-1];

        int nr_rand_tt_assigns;

        int level_dist[65]; // How many steps are below a certain level

        Vec_Int_t* vLits; // Dynamic vector of literals for clause generation

        int conflict_limit;
        
        synth_spec()
        {
            vLits = Vec_IntAlloc(0);
            conflict_limit = 0;
            solver_alloc(&_solver);
        }

        ~synth_spec()
        {
            solver_dealloc(&_solver);
            Vec_IntFree(vLits);
        }

        Solver solver() const
        {
            return _solver;
        }

        void solver_init()
        {
            solver_restart(&_solver);
        }

        void update_level_map(fence& f)
        {
            nr_levels = f.nr_levels();
            level_dist[0] = nr_in;
            for (int i = 1; i <= nr_levels; i++) {
                level_dist[i] = level_dist[i-1] + f[i-1];
            }
        }

        /***********************************************************************
            Returns the level (in the Boolean chain) of the specified step.
        ***********************************************************************/
        int get_level(int step_idx) const
        {
            if (step_idx == nr_in) { // First step is always on level 1
                return 1;
            }
            for (int i = 0; i <= nr_levels; i++) {
                if (level_dist[i] > step_idx) {
                    return i;
                }
            }
            return -1;
        }

        /***********************************************************************
            Returns the index of the first step on the specified level.
        ***********************************************************************/
        int first_step_on_level(int level) const
        {
            if (level == 0) { return 0; }
            return level_dist[level-1];
        }

    };
    
    /***************************************************************************
        Used to gather data on synthesis experiments.
    ***************************************************************************/
    struct synth_stats
    {
        double overhead = 0;
        double total_synth_time = 0;
        double time_to_first_synth = 0;
    };
    
    /***************************************************************************
        We consider a truth table to be trivial if it is equal to (or the
        complement of) a primary input or constant zero.
    ***************************************************************************/
    template<typename TT>
    static inline bool is_trivial(const TT& tt)
    {
        TT tt_check;

        if (tt == tt_check || tt == ~tt_check) {
            return true;
        }

        for (int i = 0; i < tt.num_vars(); i++) {
            kitty::create_nth_var(tt_check, i);
            if (tt == tt_check || tt == ~tt_check) {
                return true;
            }
        }

        return false;
    }

    static inline bool is_trivial(const dynamic_truth_table& tt)
    {
        dynamic_truth_table tt_check(tt.num_vars());

        if (tt == tt_check || tt == ~tt_check) {
            return true;
        }

        for (int i = 0; i < tt.num_vars(); i++) {
            kitty::create_nth_var(tt_check, i);
            if (tt == tt_check || tt == ~tt_check) {
                return true;
            }
        }

        return false;
    }

    

    template<typename TT, typename Solver>
    static inline int 
    get_sim_var(const synth_spec<TT,Solver>& spec, int i, int t)
    {
        assert(i < spec.nr_steps);
        assert(t < spec.nr_sim_vars );

        return spec.sim_offset + spec.tt_size * i + t;
    }

    template<typename TT, typename Solver>
    static inline int 
    get_out_var(const synth_spec<TT,Solver>& spec, int h, int i)
    {
        assert(h < spec.nr_nontriv);
        assert(i < spec.nr_steps);

        return spec.out_offset + spec.nr_steps * h + i;
    }

    template<typename TT, typename Solver>
    static inline int
    get_op_var(const synth_spec<TT,Solver>& spec, int i, int c, int b)
    {
        assert(i < spec.nr_steps);
        assert(b < 2 );
        assert(c < 2 );
        assert(b > 0 || c > 0);

        return spec.steps_offset + i * 3 + ( c << 1 ) + b - 1;
    }

    template<typename TT, typename Solver>
    static inline int
    get_op_var(const synth_spec<TT,Solver>& spec, int i, int d, int c, int b)
    {
        assert(i < spec.nr_steps);
        assert(b < 2 );
        assert(c < 2 );
        assert(d < 2 );
        assert(b > 0 || c > 0 || d > 0);

        return spec.steps_offset + i * 7 + (d << 2) + ( c << 1 ) + b - 1;
    }

    template<typename TT, typename Solver>
    static inline int
    get_sel_var(const synth_spec<TT,Solver>& spec, int i, int j, int k)
    {
        int offset = 0;

        assert(i < spec.nr_steps);
        assert(k < spec.nr_in + i);
        assert(j < k);

        offset = spec.sel_offset;
        for (int a = spec.nr_in; a < spec.nr_in + i; a++)
            offset += a * ( a - 1 ) / 2;

        return offset + (-j * ( 1 + j - 2 * ( spec.nr_in + i ) ) ) / 2 +
            (k - j - 1);
    }

    template<typename TT, typename Solver>
    static inline int
    get_sel_var(const synth_spec<TT,Solver>& spec, int i, int j, int k, int l)
    {
        int offset = 0;

        assert(i < spec.nr_steps);
        assert(l < spec.nr_in + i);
        assert(k < l);
        assert(j < k);

        offset = spec.sel_offset;
        for (int a = spec.nr_in; a < spec.nr_in + i; a++) {
            offset += (a * (a - 1) * (a - 2)) / 6;
        }
        
        for (int lp = 2; lp < spec.nr_in+i; lp++) {
            for (int kp = 1; kp < lp; kp++) {
                for (int jp = 0; jp < kp; jp++) {
                    if ((lp < l) || ((lp == l) && (kp < k)) || 
                            ((lp == l) && (kp == k) && (jp < j))) {
                        offset++;
                    }
                }
            }
        }

        return offset;
    }

    template<typename TT, typename Solver>
    static inline int
    get_fence_var(const synth_spec<TT,Solver>& spec, int idx)
    {
        return spec.fence_offset + idx;
    }

    template<typename TT, typename Solver>
    static void
    print_solver_state(const synth_spec<TT,Solver>& spec)
    {
        printf("\n");
        printf("========================================"
                "========================================\n");
        printf("  SOLVER STATE\n\n");

        for (int i = 0; i < spec.nr_steps; i++) {
            for (int k = 1; k < spec.nr_in+i; k++) {
                for (int j = 0; j < k; j++) {
                    if (solver_var_value(spec.solver(), 
                                get_sel_var(spec, i, j, k))) {
                        printf("  x_%d has inputs x_%d and x_%d\n",
                                spec.nr_in+i+1, j+1, k+1);
                    }
                }
            }
            printf("  f_%d = ", spec.nr_in+i+1);
            printf("%d", solver_var_value(spec.solver(), 
                        get_op_var(spec, i, 1, 1)));
            printf("%d", solver_var_value(spec.solver(), 
                        get_op_var(spec, i, 1, 0)));
            printf("%d", solver_var_value(spec.solver(), 
                        get_op_var(spec, i, 0, 1)));
            printf("0\n");
            printf("  tt_%d = ",spec.nr_in+ i+1);
            for (int t = spec.tt_size - 1; t >= 0; t--) {
                printf("%d", solver_var_value(spec.solver(), 
                            get_sim_var(spec, i, t)));
            }
            printf("0\n\n");
        }

        for (int h = 0; h < spec.nr_nontriv; h++) {
            for (int i = 0; i < spec.nr_steps; i++) {
                if (solver_var_value(spec.solver(), get_out_var(spec, h, i))) {
                    printf("  g_%d --> x_%d\n", h+1, spec.nr_in+i+1);
                }
            }
        }

        for (int h = 0; h < spec.nr_nontriv; h++) {
            for (int i = 0; i < spec.nr_steps; i++) {
                printf("  g_%d_%d=%d\n", h+1, spec.nr_in+i+1,
                        solver_var_value(spec.solver(), get_out_var(spec, h, i))
                        );
            }
        }
        printf("\n");
        
        for (int i = 0; i < spec.nr_steps; i++) {
            for (int k = 1; k < spec.nr_in+i; k++) {
                for (int j = 0; j < k; j++) {
                    printf("s_%d_%d_%d=%d\n", spec.nr_in+i+1, j+1, k+1,
                            solver_var_value(spec.solver(), 
                                get_sel_var(spec, i, j, k)));
                }
            }
            printf("\n");
            printf("f_%d_0_0=0\n", spec.nr_in+i+1);
            printf("f_%d_0_1=%d\n", spec.nr_in+i+1, solver_var_value(spec.solver(), 
                        get_op_var(spec, i, 0, 1)));
            printf("f_%d_1_0=%d\n", spec.nr_in+i+1, solver_var_value(spec.solver(),
                        get_op_var(spec, i, 1, 0)));
            printf("f_%d_1_1=%d\n", spec.nr_in+i+1, solver_var_value(spec.solver(), 
                        get_op_var(spec, i, 1, 1)));
            printf("\n");
            for (int t = spec.tt_size - 1; t >= 0; t--) {
                printf("x_%d_%d=%d\n", spec.nr_in+i+1, t+1, solver_var_value(spec.solver(), 
                            get_sim_var(spec, i, t)));
            }
            printf("x_%d_0=0\n", spec.nr_in+i);
            printf("\n");
        }
        printf("\n");
            
        printf("========================================"
               "========================================\n");
    }

    template<typename TT, typename Solver>
    static void
    print_solver_state3(const synth_spec<TT,Solver>& spec)
    {
        printf("\n");
        printf("========================================"
                "========================================\n");
        printf("  SOLVER STATE\n\n");

        for (int i = 0; i < spec.nr_steps; i++) {
            for (int l = 2; l < spec.nr_in+i; l++) {
                for (int k = 1; k < l; k++) {
                    for (int j = 0; j < k; j++) {
                        if (solver_var_value(spec.solver(), 
                                    get_sel_var(spec, i, j, k, l))) {
                            printf("  x_%d has inputs x_%d, x_%d, and x_%d\n",
                                    spec.nr_in+i+1, j+1, k+1, l+1);
                        }
                    }
                }
            }
            printf("  f_%d = ", spec.nr_in+i+1);
            printf("%d", solver_var_value(spec.solver(), 
                        get_op_var(spec, i, 1, 1, 1)));
            printf("%d", solver_var_value(spec.solver(), 
                        get_op_var(spec, i, 1, 1, 0)));
            printf("%d", solver_var_value(spec.solver(), 
                        get_op_var(spec, i, 1, 0, 1)));
            printf("%d", solver_var_value(spec.solver(), 
                        get_op_var(spec, i, 1, 0, 0)));
            printf("%d", solver_var_value(spec.solver(), 
                        get_op_var(spec, i, 0, 1, 1)));
            printf("%d", solver_var_value(spec.solver(), 
                        get_op_var(spec, i, 0, 1, 0)));
            printf("%d", solver_var_value(spec.solver(), 
                        get_op_var(spec, i, 0, 0, 1)));
            printf("0\n");
            printf("  tt_%d = ", spec.nr_in+i+1);
            for (int t = spec.tt_size - 1; t >= 0; t--) {
                printf("%d", solver_var_value(spec.solver(), 
                            get_sim_var(spec, i, t)));
            }
            printf("0\n\n");
        }

        for (int h = 0; h < spec.nr_nontriv; h++) {
            for (int i = 0; i < spec.nr_steps; i++) {
                if (solver_var_value(spec.solver(), get_out_var(spec, h, i))) {
                    printf("  g_%d --> x_%d\n", h+1, spec.nr_in+i+1);
                }
            }
        }

        for (int h = 0; h < spec.nr_nontriv; h++) {
            for (int i = 0; i < spec.nr_steps; i++) {
                printf("  g_%d_%d=%d\n", h+1, spec.nr_in+i+1,
                        solver_var_value(spec.solver(), get_out_var(spec, h, i))
                        );
            }
        }
        printf("\n");
        
        for (int i = 0; i < spec.nr_steps; i++) {
            for (int l = 2; l < spec.nr_in+i; l++) {
                for (int k = 1; k < l; k++) {
                    for (int j = 0; j < k; j++) {
                        printf("s_%d_%d_%d_%d=%d\n", spec.nr_in+i+1, j+1, k+1, l+1,
                                solver_var_value(spec.solver(), 
                                    get_sel_var(spec, i, j, k, l)));
                    }
                }
            }
            printf("\n");
            printf("f_%d_0_0_0=0\n", i);
            printf("f_%d_0_0_1=%d\n", spec.nr_in+i+1, solver_var_value(spec.solver(), 
                        get_op_var(spec, i, 0, 0, 1)));
            printf("f_%d_0_1_0=%d\n", spec.nr_in+i+1, solver_var_value(spec.solver(),
                        get_op_var(spec, i, 0, 1, 0)));
            printf("f_%d_0_1_1=%d\n", spec.nr_in+i+1, solver_var_value(spec.solver(), 
                        get_op_var(spec, i, 0, 1, 1)));
            printf("f_%d_1_0_0=%d\n", spec.nr_in+i+1, solver_var_value(spec.solver(), 
                        get_op_var(spec, i, 1, 0, 0)));
            printf("f_%d_1_0_1=%d\n", spec.nr_in+i+1, solver_var_value(spec.solver(), 
                        get_op_var(spec, i, 1, 0, 1)));
            printf("f_%d_1_1_0=%d\n", spec.nr_in+i+1, solver_var_value(spec.solver(), 
                        get_op_var(spec, i, 1, 1, 0)));
            printf("f_%d_1_1_1=%d\n", spec.nr_in+i+1, solver_var_value(spec.solver(), 
                        get_op_var(spec, i, 1, 1, 1)));
            printf("\n");
            for (int t = spec.tt_size - 1; t >= 0; t--) {
                printf("x_%d_%d=%d\n", spec.nr_in+i+1, t+1, solver_var_value(spec.solver(), 
                            get_sim_var(spec, i, t)));
            }
            printf("x_%d_0=0\n", spec.nr_in+i);
            printf("\n");
        }
        printf("\n");
            
        printf("========================================"
               "========================================\n");
    }

    /***************************************************************************
        Normalize outputs by converting them to normal function.  Also check
        for trivial outputs, such as constant functions or projections. This
        determines which of the specifeid functions need to be synthesized.
        This function expects the following invariants to hold:
            (1) The number of input variables has been set.
            (2) The number of output variables has been set.
            (3) The functions requested to be synthesized have been set.
    ***************************************************************************/
    template<typename TT, typename Solver>
    void spec_preprocess(synth_spec<TT,Solver>& spec) 
    {
        spec.tt_size = (1 << spec.nr_in) - 1;

        if (spec.verbosity) {
            printf("\n");
            printf("========================================"
                   "========================================\n");
            printf("  Pre-processing for %s:\n", spec.nr_out > 1 ? 
                    "functions" : "function");
            for (int h = 0; h < spec.nr_out; h++) {
                printf("  ");
                kitty::print_binary(*spec.functions[h], std::cout);
                printf("\n");
            }
            printf("========================================"
                   "========================================\n");
            printf("  SPEC:\n");
            printf("\tnr_in=%d\n", spec.nr_in);
            printf("\tnr_out=%d\n", spec.nr_out);
            printf("\ttt_size=%d\n", spec.tt_size);
        }

        // Detect any trivial outputs.
        spec.nr_triv = 0;
        spec.nr_nontriv = 0;
        spec.out_inv = 0;
        spec.triv_flag = 0;
        for (int h = 0; h < spec.nr_out; h++) {
            if (is_const0(*spec.functions[h])) {
                spec.triv_flag |= (1 << h);
                spec.triv_functions[spec.nr_triv++] = 0;
            } else if (is_const0(~(*spec.functions[h]))) {
                spec.triv_flag |= (1 << h);
                spec.triv_functions[spec.nr_triv++] = 0;
                spec.out_inv |= (1 << h);
            } else {
                TT tt_var;
                for (int i = 0; i < spec.nr_in; i++) {
                    create_nth_var(tt_var, i);
                    if (*spec.functions[h] == tt_var) {
                        spec.triv_flag |= (1 << h);
                        spec.triv_functions[spec.nr_triv++] = i+1;
                        break;
                    } else if (*spec.functions[h] == ~(tt_var)) {
                        spec.triv_flag |= (1 << h);
                        spec.triv_functions[spec.nr_triv++] = i+1;
                        spec.out_inv |= (1 << h);
                        break;
                    }
                }
                // Even when the output is not trivial, we still need to ensure
                // that it's normal.
                if (!((spec.triv_flag >> h) & 1)) {
                    if (!is_normal(*spec.functions[h])) {
                        spec.out_inv |= (1 << h);
                    }
                    spec.synth_functions[spec.nr_nontriv++] = h;
                }
            }
        }

        if (spec.verbosity) {
            for (int h = 0; h < spec.nr_out; h++) {
                if ((spec.triv_flag >> h) & 1) {
                    printf("  Output %d is trivial\n", h+1);
                }
                if ((spec.out_inv >> h) & 1) {
                    printf("  Inverting output %d\n", h+1);
                }
            }
            printf("  Trivial outputs=%d\n", spec.nr_triv);
            printf("  Non-trivial outputs=%d\n", spec.nr_out-spec.nr_triv);
            printf("========================================"
                    "========================================\n");
            printf("\n");
        }
    }


    template<typename Solver>
    void spec_preprocess(synth_spec<dynamic_truth_table,Solver>& spec) 
    {
        spec.tt_size = (1 << spec.nr_in) - 1;

        if (spec.verbosity) {
            printf("\n");
            printf("========================================"
                   "========================================\n");
            printf("  Pre-processing for %s:\n", spec.nr_out > 1 ? 
                    "functions" : "function");
            for (int h = 0; h < spec.nr_out; h++) {
                printf("  ");
                kitty::print_binary(*spec.functions[h], std::cout);
                printf("\n");
            }
            printf("========================================"
                   "========================================\n");
            printf("  SPEC:\n");
            printf("\tnr_in=%d\n", spec.nr_in);
            printf("\tnr_out=%d\n", spec.nr_out);
            printf("\ttt_size=%d\n", spec.tt_size);
        }

        // Detect any trivial outputs.
        spec.nr_triv = 0;
        spec.nr_nontriv = 0;
        spec.out_inv = 0;
        spec.triv_flag = 0;
        for (int h = 0; h < spec.nr_out; h++) {
            if (is_const0(*spec.functions[h])) {
                spec.triv_flag |= (1 << h);
                spec.triv_functions[spec.nr_triv++] = 0;
            } else if (is_const0(~(*spec.functions[h]))) {
                spec.triv_flag |= (1 << h);
                spec.triv_functions[spec.nr_triv++] = 1;
            } else {
                dynamic_truth_table tt_var(spec.nr_in);
                for (int i = 0; i < spec.nr_in; i++) {
                    create_nth_var(tt_var, i);
                    if (*spec.functions[h] == tt_var) {
                        spec.triv_flag |= (1 << h);
                        spec.triv_functions[spec.nr_triv++] = (i+1) << 1;
                        break;
                    } else if (*spec.functions[h] == ~(tt_var)) {
                        spec.triv_flag |= (1 << h);
                        spec.triv_functions[spec.nr_triv++] = ((i+1) << 1) + 1;
                        break;
                    }
                }
                // Even when the output is not trivial, we still need to ensure
                // that it's normal.
                if (!((spec.triv_flag >> h) & 1)) {
                    if (!is_normal(*spec.functions[h])) {
                        spec.out_inv |= (1 << h);
                    }
                    spec.synth_functions[spec.nr_nontriv++] = h;
                }
            }
        }

        if (spec.verbosity) {
            for (int h = 0; h < spec.nr_out; h++) {
                if ((spec.triv_flag >> h) & 1) {
                    printf("  Output %d is trivial\n", h+1);
                }
                if ((spec.out_inv >> h) & 1) {
                    printf("  Inverting output %d\n", h+1);
                }
            }
            printf("  Trivial outputs=%d\n", spec.nr_triv);
            printf("  Non-trivial outputs=%d\n", spec.nr_out-spec.nr_triv);
            printf("========================================"
                    "========================================\n");
            printf("\n");
        }
    }

    /***************************************************************************
        Extracts a Boolean chain from a satisfiable solution.
    ***************************************************************************/
    template<typename TT, typename Solver>
    void chain_extract(synth_spec<TT,Solver>& spec, chain<TT,2>& chain)
    {
        int op_inputs[2];

        chain.reset(spec.nr_in, spec.nr_out, spec.nr_steps);

        for (int i = 0; i < spec.nr_steps; i++) {
            kitty::static_truth_table<2> op;
            if (solver_var_value(spec.solver(), get_op_var(spec, i, 0, 1 )))
                kitty::set_bit(op, 1); 
            if (solver_var_value(spec.solver(), get_op_var(spec, i, 1, 0)))
                kitty::set_bit(op, 2); 
            if (solver_var_value(spec.solver(), get_op_var(spec, i, 1, 1)))
                kitty::set_bit(op, 3); 
            
            if (spec.verbosity) {
                printf("  step x_%d performs operation\n  ", i+spec.nr_in+1);
                kitty::print_binary(op, std::cout);
                printf("\n");
            }

            for (int k = 1; k < spec.nr_in + i; k++) {
                for (int j = 0; j < k; j++) {
                    if (solver_var_value(spec.solver(),
                                get_sel_var(spec, i, j, k)))
                    {
                        if (spec.verbosity) {
                            printf("  with operands x_%d and x_%d", j+1, k+1);
                        }
                        op_inputs[0] = j;
                        op_inputs[1] = k;
                        chain.set_step(i, op, op_inputs);
                        break;
                    }

                }
            }
            if (spec.verbosity) {
                printf("\n");
            }
        }

        auto triv_count = 0, nontriv_count = 0;
        for (int h = 0; h < spec.nr_out; h++) {
            printf("out=%d\n");
            if ((spec.triv_flag >> h) & 1) {
                chain.set_out(h, (spec.triv_functions[triv_count++] << 1) +
                        ((spec.out_inv >> h) & 1));
                printf("TRIV inv flag=%d\n", ((spec.out_inv >> h) & 1));
                continue;
            }
            for (int i = 0; i < spec.nr_steps; i++) {
                printf("nontriv\n");
                if (solver_var_value(spec.solver(), 
                            get_out_var(spec, nontriv_count, i))) {
                    chain.set_out(h, ((i + spec.nr_in + 1) << 1) +
                            ((spec.out_inv >> h) & 1));
                    nontriv_count++;
                    break;
                }
            }
        }
    }


    template<typename TT, typename Solver>
    void top_chain_extract(synth_spec<TT,Solver>& spec, chain<TT,2>& chain)
    {
        int op_inputs[2];

        chain.reset(spec.nr_in, spec.nr_out, spec.nr_steps);

        for (int i = 0; i < spec.nr_steps; i++) {
            kitty::static_truth_table<2> op;
            if (solver_var_value(spec.solver(), get_op_var(spec, i, 0, 1 )))
                kitty::set_bit(op, 1); 
            if (solver_var_value(spec.solver(), get_op_var(spec, i, 1, 0)))
                kitty::set_bit(op, 2); 
            if (solver_var_value(spec.solver(), get_op_var(spec, i, 1, 1)))
                kitty::set_bit(op, 3); 
            
            if (spec.verbosity) {
                printf("  step x_%d performs operation\n  ", i+spec.nr_in+1);
                kitty::print_binary(op, std::cout);
                printf("\n");
            }
            
            auto level = spec.get_level(i + spec.nr_in);
            assert(level > 0);

            for (auto k = spec.first_step_on_level(level-1); 
                    k < spec.first_step_on_level(level); k++) {
                for (int j = 0; j < k; j++) {
                    if (solver_var_value(spec.solver(),
                                spec.selection_vars[i][j][k]))
                    {
                        if (spec.verbosity) {
                            printf("  with operands x_%d and x_%d", j+1, k+1);
                        }
                        op_inputs[0] = j;
                        op_inputs[1] = k;
                        chain.set_step(i, op, op_inputs);
                        break;
                    }

                }
            }
            if (spec.verbosity) {
                printf("\n");
            }
        }

        auto triv_count = 0, nontriv_count = 0;
        for (int h = 0; h < spec.nr_out; h++) {
            if ((spec.triv_flag >> h) & 1) {
                chain.set_out(h, (spec.triv_functions[triv_count++] << 1) +
                        ((spec.out_inv >> h) & 1));
                continue;
            }
            for (int i = 0; i < spec.nr_steps; i++) {
                if (solver_var_value(spec.solver(), 
                            get_out_var(spec, nontriv_count, i))) {
                    chain.set_out(h, ((i + spec.nr_in + 1) << 1) +
                            ((spec.out_inv >> h) & 1));
                    nontriv_count++;
                    break;
                }
            }
        }
    }

    template<typename TT, typename Solver>
    void chain_extract3(synth_spec<TT,Solver>& spec, chain<TT,3>& chain)
    {
        int op_inputs[3];

        chain.reset(spec.nr_in, spec.nr_out, spec.nr_steps);

        for (int i = 0; i < spec.nr_steps; i++) {
            kitty::static_truth_table<3> op;
            if (solver_var_value(spec.solver(), get_op_var(spec, i, 0, 0, 1)))
                kitty::set_bit(op, 1); 
            if (solver_var_value(spec.solver(), get_op_var(spec, i, 0, 1, 0)))
                kitty::set_bit(op, 2); 
            if (solver_var_value(spec.solver(), get_op_var(spec, i, 0, 1, 1)))
                kitty::set_bit(op, 3); 
            if (solver_var_value(spec.solver(), get_op_var(spec, i, 1, 0, 0)))
                kitty::set_bit(op, 4); 
            if (solver_var_value(spec.solver(), get_op_var(spec, i, 1, 0, 1)))
                kitty::set_bit(op, 5); 
            if (solver_var_value(spec.solver(), get_op_var(spec, i, 1, 1, 0)))
                kitty::set_bit(op, 6); 
            if (solver_var_value(spec.solver(), get_op_var(spec, i, 1, 1, 1)))
                kitty::set_bit(op, 7); 
            
            if (spec.verbosity) {
                printf("  step x_%d performs operation\n  ", i+spec.nr_in+1);
                kitty::print_binary(op, std::cout);
                printf("\n");
            }

            for (int l = 2; l < spec.nr_in + i; l++) {
                for (int k = 1; k < l; k++) {
                    for (int j = 0; j < k; j++) {
                        if (solver_var_value(spec.solver(),
                                    get_sel_var(spec, i, j, k, l)))
                        {
                            if (spec.verbosity) {
                                printf("  with operands x_%d, x_%d, and x_%d",
                                        j+1, k+1, l+1);
                            }
                            op_inputs[0] = j;
                            op_inputs[1] = k;
                            op_inputs[2] = l;
                            chain.set_step(i, op, op_inputs);
                            break;
                        }
                    }
                }
            }
            if (spec.verbosity) {
                printf("\n");
            }
        }

        auto triv_count = 0, nontriv_count = 0;
        for (int h = 0; h < spec.nr_out; h++) {
            if ((spec.triv_flag >> h) & 1) {
                chain.set_out(h, (spec.triv_functions[triv_count++] << 1) +
                        ((spec.out_inv >> h) & 1));
                continue;
            }
            for (int i = 0; i < spec.nr_steps; i++) {
                if (solver_var_value(spec.solver(), 
                            get_out_var(spec, nontriv_count, i))) {
                    chain.set_out(h, ((i + spec.nr_in + 1) << 1) +
                            ((spec.out_inv >> h) & 1));
                    nontriv_count++;
                    break;
                }
            }
        }
        assert(triv_count+nontriv_count == spec.nr_out);
    }


    /***************************************************************************
        Extracts only the underlying DAG structure from a solution.
    ***************************************************************************/
    template<typename TT, typename Solver>
    void dag_extract(synth_spec<TT,Solver>& spec, dag& dag)
    {
        dag.reset(spec.nr_in, spec.nr_steps);

        for (int i = 0; i < spec.nr_steps; i++) {
            for (int k = 1; k < spec.nr_in + i; k++) {
                for (int j = 0; j < k; j++) {
                    if (solver_var_value(spec.solver(),
                                get_sel_var(spec, i, j, k)))
                    {
                        dag.set_vertex(i, j, k);
                        break;
                    }

                }
            }
        }
    }

    template<typename T, typename TT, typename Solver>
    synth_result 
    chain_exists(T* synth, synth_spec<TT,Solver>& spec)
    {
        if (spec.verbosity) {
            printf("  Existence check with %d steps...\n", spec.nr_steps);
        }

        synth->add_clauses(spec);

        auto status = solver_solve(spec.solver(), 0, 0, spec.conflict_limit);

        if (spec.verbosity) {
            if (status == success) {
                printf("  SUCCESS\n\n"); 
            } else if (status == failure) {
                printf("  FAILURE\n\n"); 
            } else {
                printf("  TIMEOUT\n\n"); 
            }
        }

        return status;
    }

    template<typename T, typename TT, typename Solver>
    synth_result 
    chain_exists3(T* synth, synth_spec<TT,Solver>& spec)
    {
        if (spec.verbosity) {
            printf("  Existence check with %d steps...\n", spec.nr_steps);
        }

        synth->add_clauses3(spec);

        auto status = solver_solve(spec.solver(), 0, 0, spec.conflict_limit);

        if (spec.verbosity) {
            if (status == success) {
                printf("  SUCCESS\n\n"); 
            } else if (status == failure) {
                printf("  FAILURE\n\n"); 
            } else {
                printf("  TIMEOUT\n\n"); 
            }
        }

        return status;
    }

    template<typename T, typename TT, typename Solver, int OpSize=2>
    synth_result 
    cegar_chain_exists(
            T* synth, synth_spec<TT,Solver>& spec, chain<TT,OpSize>& chain)
    {
        if (spec.verbosity) {
            printf("  Existence check with %d steps...\n", spec.nr_steps);
        }

        synth->cegar_add_clauses(spec);
        for (int i = 0; i < spec.nr_rand_tt_assigns; i++) {
            if (!create_tt_clauses(spec, rand() % spec.tt_size)) {
                return failure;
            }
        }

        while (true) {
            auto status = solver_solve(spec.solver(), 0, 0, spec.conflict_limit);
            if (status == success) {
                if (spec.verbosity > 1) {
                    print_solver_state(spec);
                }
                chain_extract(spec, chain);
                auto sim_tts = chain.simulate();
                auto xor_tt = (*sim_tts[0]) ^ (*spec.functions[0]);
                auto first_one = kitty::find_first_one_bit(xor_tt);
                if (first_one == -1) {
                    if (spec.verbosity) {
                        printf("  SUCCESS\n\n"); 
                    }
                    return success;
                }
                // Add additional constraint.
                if (spec.verbosity) {
                    printf("  CEGAR difference at tt index %ld\n", first_one);
                }
                if (!create_tt_clauses(spec, first_one-1)) {
                    return failure;
                }
            } else {
                if (spec.verbosity) {
                    if (status == failure) {
                        printf("  FAILURE\n\n"); 
                    } else {
                        printf("  TIMEOUT\n\n"); 
                    }
                }
                return status;
            }
        }
    }

    template<typename T, typename TT, typename Solver, int OpSize=2>
    synth_result 
    cegar_top_chain_exists(
            T* synth, synth_spec<TT,Solver>& spec, chain<TT,OpSize>& chain)
    {
        if (spec.verbosity) {
            printf("  Existence check with %d steps...\n", spec.nr_steps);
        }

        synth->cegar_add_clauses(spec);
        for (int i = 0; i < spec.nr_rand_tt_assigns; i++) {
            if (!top_create_tt_clauses(spec, rand() % spec.tt_size)) {
                return failure;
            }
        }

        while (true) {
            auto status = solver_solve(spec.solver(), 0, 0, spec.conflict_limit);
            if (status == success) {
                if (spec.verbosity > 1) {
                    print_solver_state(spec);
                }
                top_chain_extract(spec, chain);
                auto sim_tts = chain.simulate();
                auto xor_tt = (*sim_tts[0]) ^ (*spec.functions[0]);
                auto first_one = kitty::find_first_one_bit(xor_tt);
                if (first_one == -1) {
                    if (spec.verbosity) {
                        printf("  SUCCESS\n\n"); 
                    }
                    return success;
                }
                // Add additional constraint.
                if (spec.verbosity) {
                    printf("  CEGAR difference at tt index %ld\n", first_one);
                }
                if (!top_create_tt_clauses(spec, first_one-1)) {
                    return failure;
                }
            } else {
                if (spec.verbosity) {
                    if (status == failure) {
                        printf("  FAILURE\n\n"); 
                    } else {
                        printf("  TIMEOUT\n\n"); 
                    }
                }
                return status;
            }
        }
    }


    /***************************************************************************
        A parallel version which periodically checks if a solution has been
        found by another thread.
    ***************************************************************************/
    template<typename T, typename TT, typename Solver, int OpSize=2>
    synth_result 
    pcegar_top_chain_exists(
            T* synth, synth_spec<TT,Solver>& spec, chain<TT,OpSize>& chain,
            bool* found)
    {
        if (spec.verbosity) {
            printf("  Existence check with %d steps...\n", spec.nr_steps);
        }

        synth->cegar_add_clauses(spec);
        for (int i = 0; i < spec.nr_rand_tt_assigns; i++) {
            if (!top_create_tt_clauses(spec, rand() % spec.tt_size)) {
                return failure;
            }
        }

        while (true) {
            auto status = solver_solve(spec.solver(), 0, 0, spec.conflict_limit);
            if (status == success) {
                if (spec.verbosity > 1) {
                    print_solver_state(spec);
                }
                top_chain_extract(spec, chain);
                auto sim_tts = chain.simulate();
                auto xor_tt = (*sim_tts[0]) ^ (*spec.functions[0]);
                auto first_one = kitty::find_first_one_bit(xor_tt);
                if (first_one == -1) {
                    if (spec.verbosity) {
                        printf("  SUCCESS\n\n"); 
                    }
                    return success;
                }
                // Add additional constraint.
                if (spec.verbosity) {
                    printf("  CEGAR difference at tt index %ld\n", first_one);
                }
                if (!top_create_tt_clauses(spec, first_one-1)) {
                    return failure;
                }
            } else if (status == timeout) {
                if (*found) {
                    return timeout;
                }
            } else {
                if (spec.verbosity) {
                    printf("  FAILURE\n\n"); 
                }
                return status;
            }
        }
    }

    template<typename T, typename TT, typename Solver>
    synth_result 
    cegar_chain_exists3(
            T* synth, synth_spec<TT,Solver>& spec, chain<TT,3>& chain)
    {
        if (spec.verbosity) {
            printf("  Existence check with %d steps...\n", spec.nr_steps);
        }

        synth->cegar_add_clauses3(spec);
        for (int i = 0; i < spec.nr_rand_tt_assigns; i++) {
            if (!create_tt_clauses3(spec, rand() % spec.tt_size)) {
                return failure;
            }
        }

        while (true) {
            auto status = solver_solve(spec.solver(), 0, 0, spec.conflict_limit);
            if (status == success) {
                if (spec.verbosity > 1) {
                    print_solver_state3(spec);
                }
                chain_extract3(spec, chain);
                assert(chain.nr_steps() == spec.nr_steps);
                auto sim_tts = chain.simulate();
                auto xor_tt = (*sim_tts[0]) ^ (*spec.functions[0]);
                auto first_one = kitty::find_first_one_bit(xor_tt);
                if (first_one == -1) {
                    if (spec.verbosity) {
                        printf("  SUCCESS\n\n"); 
                    }
                    return success;
                }
                // Add additional constraint.
                if (spec.verbosity) {
                    printf("  CEGAR difference at tt index %ld\n", first_one);
                }
                if (!create_tt_clauses3(spec, first_one-1)) {
                    return failure;
                }
            } else {
                if (spec.verbosity) {
                    if (status == failure) {
                        printf("  FAILURE\n\n"); 
                    } else {
                        printf("  TIMEOUT\n\n"); 
                    }
                }
                return status;
            }
        }
    }

    template<typename S, typename TT, typename Solver, int OpSize=2>
    synth_result
    std_synthesize(
            S* synth, synth_spec<TT,Solver>& spec, chain<TT,OpSize>& chain)
    {
        assert(spec.nr_in <= 6);
        assert(spec.nr_out <= 64);

        spec_preprocess(spec);
        
        // The special case when the Boolean chain to be synthesized consists
        // entirely of trivial functions.
        if (spec.nr_triv == spec.nr_out) {
            chain.reset(spec.nr_in, spec.nr_out, 0);
            for (int h = 0; h < spec.nr_out; h++) {
                chain.set_out(h, (spec.triv_functions[h] << 1) + 
                        ((spec.out_inv >> h) & 1));
            }
            return success;
        }

        spec.nr_steps = 1;
        while (true) {
            auto result = chain_exists<S>(synth, spec);
            if (result == success) {
                chain_extract(spec, chain);
                return success;
            } else if (result == failure) {
                spec.nr_steps++;
            } else {
                return timeout;
            }
        }
    }

    template<typename S, typename TT, typename Solver, int OpSize=2>
    synth_result
    std_synthesize3(
            S* synth, synth_spec<TT,Solver>& spec, chain<TT,OpSize>& chain)
    {
        assert(spec.nr_in <= 6);
        assert(spec.nr_out <= 64);

        spec_preprocess(spec);
        
        // The special case when the Boolean chain to be synthesized consists
        // entirely of trivial functions.
        if (spec.nr_triv == spec.nr_out) {
            chain.reset(spec.nr_in, spec.nr_out, 0);
            for (int h = 0; h < spec.nr_out; h++) {
                chain.set_out(h, (spec.triv_functions[h] << 1) +
                        ((spec.out_inv >> h) & 1));
            }
            return success;
        }

        spec.nr_steps = 1;
        while (true) {
            auto result = chain_exists3<S>(synth, spec);
            if (result == success) {
                chain_extract3(spec, chain);
                return success;
            } else if (result == failure) {
                spec.nr_steps++;
            } else  {
                return timeout;
            }
        }
    }

    /***************************************************************************
        Performs exact synthesis using a CEGAR loop.
    ***************************************************************************/
    template<typename S, typename TT, typename Solver, int OpSize=2>
    synth_result
    cegar_std_synthesize(
            S* synth, synth_spec<TT,Solver>& spec, chain<TT,OpSize>& chain)
    {
        assert(spec.nr_in <= 6);
        assert(spec.nr_out <= 64);

        spec_preprocess(spec);

        spec.nr_rand_tt_assigns = 2*spec.nr_in;

        // The special case when the Boolean chain to be synthesized consists
        // entirely of trivial functions.
        if (spec.nr_triv == spec.nr_out) {
            chain.reset(spec.nr_in, spec.nr_out, 0);
            for (int h = 0; h < spec.nr_out; h++) {
                chain.set_out(h, (spec.triv_functions[h] << 1) + 
                        ((spec.out_inv >> h) & 1));
            }
            return success;
        }

        spec.nr_steps = 1;
        while (true) {
            auto status = cegar_chain_exists<S>(synth, spec, chain);
            if (status == success) {
                return success;
            } else if (status == failure) {
                spec.nr_steps++;
            } else {
                return timeout;
            }
        }
    }

    template<typename S, typename TT, typename Solver, int OpSize=2>
    synth_result
    cegar_std_synthesize3(
            S* synth, synth_spec<TT,Solver>& spec, chain<TT,OpSize>& chain)
    {
        assert(spec.nr_in <= 6);
        assert(spec.nr_out <= 64);

        spec_preprocess(spec);

        spec.nr_rand_tt_assigns = 2*spec.nr_in;

        // The special case when the Boolean chain to be synthesized consists
        // entirely of trivial functions.
        if (spec.nr_triv == spec.nr_out) {
            chain.reset(spec.nr_in, spec.nr_out, 0);
            for (int h = 0; h < spec.nr_out; h++) {
                chain.set_out(h, (spec.triv_functions[h] << 1) + 
                        ((spec.out_inv >> h) & 1));
            }
            return success;
        }

        spec.nr_steps = 1;
        while (true) {
            auto status = cegar_chain_exists3<S>(synth, spec, chain);
            if (status == success) {
                return success;
            } else if (status == failure) {
                spec.nr_steps++;
            } else {
                return timeout;
            }
        }
    }

    template<typename S, typename TT, typename Solver, int OpSize=2>
    synth_result
    top_synthesize(
            S* synth, synth_spec<TT,Solver>& spec, chain<TT,OpSize>& chain)
    {
        assert(spec.nr_in <= 6);
        assert(spec.nr_out <= 64);

        spec_preprocess(spec);
        
        // The special case when the Boolean chain to be synthesized consists
        // entirely of trivial functions.
        if (spec.nr_triv == spec.nr_out) {
            chain.reset(spec.nr_in, spec.nr_out, 0);
            for (int h = 0; h < spec.nr_out; h++) {
                chain.set_out(h, (spec.triv_functions[h] << 1) +
                        ((spec.out_inv >> h) & 1));
            }
            return success;
        }

        // As the topological synthesizer decomposes the synthesis problem,
        // to fairly count the total number of conflicts we should keep track
        // of all conflicts in existence checks.
        int total_conflicts = 0;
        fence f;
        po_filter<unbounded_generator> g(unbounded_generator(), 1, 2);
        int old_nnodes = 1;
        while (true) {
            g.next_fence(f);
            spec.nr_steps = f.nr_nodes();
            spec.update_level_map(f);
            
            if (spec.nr_steps > old_nnodes) {
                // Reset conflict count, since this is where other synthesizers
                // reset it.
                total_conflicts = 0;
                old_nnodes = spec.nr_steps;
            }

            if (spec.verbosity) {
                printf("  next fence:\n");
                print_fence(f);
                printf("\n");
                printf("nr_nodes=%d, nr_levels=%d\n", f.nr_nodes(), 
                        f.nr_levels());
                for (int i = 0; i < f.nr_levels(); i++) {
                    printf("f[%d] = %d\n", i, f[i]);
                }
            }
            // Add the clauses that encode the main constraints, but not
            // yet any DAG structure.
            auto status = chain_exists<S>(synth, spec);
            if (status == success) {
                top_chain_extract(spec, chain);
                return success;
            } else if (status == failure) {
                total_conflicts += solver_nr_conflicts(spec.solver());
                if (spec.conflict_limit &&
                        total_conflicts > spec.conflict_limit) {
                    return timeout;
                }
                continue;
            } else {
                return timeout;
            }
        }
    }

    template<typename S, typename TT, typename Solver, int OpSize=2>
    synth_result
    top_synthesize3(
            S* synth, synth_spec<TT,Solver>& spec, chain<TT,OpSize>& chain)
    {
        assert(spec.nr_in <= 6);
        assert(spec.nr_out <= 64);

        spec_preprocess(spec);
        
        // The special case when the Boolean chain to be synthesized consists
        // entirely of trivial functions.
        if (spec.nr_triv == spec.nr_out) {
            chain.reset(spec.nr_in, spec.nr_out, 0);
            for (int h = 0; h < spec.nr_out; h++) {
                chain.set_out(h, (spec.triv_functions[h] << 1) +
                        ((spec.out_inv >> h) & 1));
            }
            return success;
        }

        fence f;
        po_filter<unbounded_generator> g(unbounded_generator(), 1, 3);
        int total_conflicts = 0;
        int old_nnodes = 1;
        while (true) {
            g.next_fence(f);
            spec.nr_steps = f.nr_nodes();
            spec.update_level_map(f);

            if (spec.nr_steps > old_nnodes) {
                // Reset conflict count, since this is where other synthesizers
                // reset it.
                total_conflicts = 0;
                old_nnodes = spec.nr_steps;
            }

            if (spec.verbosity) {
                printf("  next fence:\n");
                print_fence(f);
                printf("\n");
                printf("nr_nodes=%d, nr_levels=%d\n", f.nr_nodes(), 
                        f.nr_levels());
                for (int i = 0; i < f.nr_levels(); i++) {
                    printf("f[%d] = %d\n", i, f[i]);
                }
            }
            // Add the clauses that encode the main constraints, but not
            // yet any DAG structure.
            auto status = chain_exists3<S>(synth, spec);
            if (status == success) {
                chain_extract3(spec, chain);
                return success;
            } else if (status == failure) {
                total_conflicts += solver_nr_conflicts(spec.solver());
                if (spec.conflict_limit &&
                        total_conflicts > spec.conflict_limit) {
                    return timeout;
                }
                continue;
            } else {
                return timeout;
            }
        }
    }

    /***************************************************************************
        Performs exact synthesis using a CEGAR loop.
    ***************************************************************************/
    template<typename S, typename TT, typename Solver, int OpSize=2>
    synth_result
    cegar_top_synthesize(
            S* synth, synth_spec<TT,Solver>& spec, chain<TT,OpSize>& chain)
    {
        assert(spec.nr_in <= 6);
        assert(spec.nr_out <= 64);

        spec_preprocess(spec);

        // The special case when the Boolean chain to be synthesized consists
        // entirely of trivial functions.
        if (spec.nr_triv == spec.nr_out) {
            chain.reset(spec.nr_in, spec.nr_out, 0);
            for (int h = 0; h < spec.nr_out; h++) {
                chain.set_out(h, (spec.triv_functions[h] << 1) +
                        ((spec.out_inv >> h) & 1));
            }
            return success;
        }

        spec.nr_rand_tt_assigns = 2*spec.nr_in;

        fence f;
        po_filter<unbounded_generator> g(unbounded_generator(), 1, 2);
        int total_conflicts = 0;
        int old_nnodes = 1;
        while (true) {
            g.next_fence(f);
            spec.nr_steps = f.nr_nodes();
            spec.update_level_map(f);

            if (spec.nr_steps > old_nnodes) {
                // Reset conflict count, since this is where other synthesizers
                // reset it.
                total_conflicts = 0;
                old_nnodes = spec.nr_steps;
            }

            if (spec.verbosity) {
                printf("  next fence:\n");
                print_fence(f);
                printf("\n");
                printf("nr_nodes=%d, nr_levels=%d\n", f.nr_nodes(), 
                        f.nr_levels());
                for (int i = 0; i < f.nr_levels(); i++) {
                    printf("f[%d] = %d\n", i, f[i]);
                }
            }
            auto status = cegar_top_chain_exists<S>(synth, spec, chain);
            if (status == success) {
                return success;
            } else if (status == failure) {
                total_conflicts += solver_nr_conflicts(spec.solver());
                if (spec.conflict_limit &&
                        total_conflicts > spec.conflict_limit) {
                    return timeout;
                }
                continue;
            } else {
                return timeout;
            }
        }
    }

    template<typename S, typename TT, typename Solver, int OpSize=2>
    synth_result
    cegar_top_synthesize3(
            S* synth, synth_spec<TT,Solver>& spec, chain<TT,OpSize>& chain)
    {
        assert(spec.nr_in <= 6);
        assert(spec.nr_out <= 64);

        spec_preprocess(spec);

        spec.nr_rand_tt_assigns = 2*spec.nr_in;

        // The special case when the Boolean chain to be synthesized consists
        // entirely of trivial functions.
        if (spec.nr_triv == spec.nr_out) {
            chain.reset(spec.nr_in, spec.nr_out, 0);
            for (int h = 0; h < spec.nr_out; h++) {
                chain.set_out(h, (spec.triv_functions[h] << 1) +
                        ((spec.out_inv >> h) & 1));
            }
            return success;
        }

        fence f;
        po_filter<unbounded_generator> g(unbounded_generator(), 1, 3);
        int total_conflicts = 0;
        int old_nnodes = 1;
        while (true) {
            g.next_fence(f);
            spec.nr_steps = f.nr_nodes();
            spec.update_level_map(f);

            if (spec.nr_steps > old_nnodes) {
                // Reset conflict count, since this is where other synthesizers
                // reset it.
                total_conflicts = 0;
                old_nnodes = spec.nr_steps;
            }

            if (spec.verbosity) {
                printf("  next fence:\n");
                print_fence(f);
                printf("\n");
                printf("nr_nodes=%d, nr_levels=%d\n", f.nr_nodes(), 
                        f.nr_levels());
                for (int i = 0; i < f.nr_levels(); i++) {
                    printf("f[%d] = %d\n", i, f[i]);
                }
            }
            auto status = cegar_chain_exists3<S>(synth, spec, chain);
            if (status == success) {
                return success;
            } else if (status == failure) {
                total_conflicts += solver_nr_conflicts(spec.solver());
                if (spec.conflict_limit &&
                        total_conflicts > spec.conflict_limit) {
                    return timeout;
                }
                continue;
            } else {
                return timeout;
            }
        }
    }

    template<typename TT, typename Solver>
    void create_variables(synth_spec<TT,Solver>& spec)
    {
        spec.solver_init();

        spec.nr_op_vars = spec.nr_steps * 3;
        spec.nr_out_vars = spec.nr_nontriv * spec.nr_steps;
        spec.nr_sim_vars = spec.nr_steps * spec.tt_size;
        spec.nr_sel_vars = 0;
        for (int i = spec.nr_in; i < spec.nr_in + spec.nr_steps; i++) {
            // TODO: right shift to make more efficient?
            spec.nr_sel_vars += ( i * ( i - 1 ) ) / 2;
        }
        spec.sel_offset = 0;
        spec.steps_offset = spec.nr_sel_vars;
        spec.out_offset = spec.nr_sel_vars + spec.nr_op_vars;
        spec.sim_offset = spec.nr_sel_vars + spec.nr_op_vars + spec.nr_out_vars;
        spec.fence_offset = spec.nr_sel_vars + spec.nr_op_vars + 
            spec.nr_out_vars + spec.nr_sim_vars;

        solver_set_nr_vars(spec.solver(), spec.nr_op_vars + spec.nr_out_vars +
                spec.nr_sim_vars + spec.nr_sel_vars);
        
        // TODO: compute better upper bound on number of literals
        Vec_IntGrowResize(spec.vLits, spec.nr_sel_vars);
    }

    template<typename TT, typename Solver>
    void top_create_variables(synth_spec<TT,Solver>& spec)
    {
        spec.solver_init();

        spec.nr_op_vars = spec.nr_steps * 3;
        spec.nr_out_vars = spec.nr_nontriv * spec.nr_steps;
        spec.nr_sim_vars = spec.nr_steps * spec.tt_size;
        spec.nr_sel_vars = 0;
        // For the other steps, ensure that they are constraint to
        // the proper level.
        for (int i = 0; i < spec.nr_steps; i++) {
            // Determine the level of this step.
            auto level = spec.get_level(i + spec.nr_in);
            assert(level > 0);
            for (auto k = spec.first_step_on_level(level-1); 
                    k < spec.first_step_on_level(level); k++) {
                for (int j = 0; j < k; j++) {
                    spec.selection_vars[i][j][k] = spec.nr_sel_vars++;
                }
            }
        }
        spec.sel_offset = 0;
        spec.steps_offset = spec.nr_sel_vars;
        spec.out_offset = spec.nr_sel_vars + spec.nr_op_vars;
        spec.sim_offset = spec.nr_sel_vars + spec.nr_op_vars + spec.nr_out_vars;
        spec.fence_offset = spec.nr_sel_vars + spec.nr_op_vars + 
            spec.nr_out_vars + spec.nr_sim_vars;

        solver_set_nr_vars(spec.solver(), spec.nr_op_vars + spec.nr_out_vars +
                spec.nr_sim_vars + spec.nr_sel_vars);
        
        // TODO: compute better upper bound on number of literals
        Vec_IntGrowResize(spec.vLits, spec.nr_sel_vars);
    }

    template<typename TT, typename Solver>
    void create_variables3(synth_spec<TT,Solver>& spec)
    {
        spec.solver_init();

        spec.nr_op_vars = spec.nr_steps * 7;
        spec.nr_out_vars = spec.nr_nontriv * spec.nr_steps;
        spec.nr_sim_vars = spec.nr_steps * spec.tt_size;
        spec.nr_sel_vars = 0;
        for (int i = spec.nr_in; i < spec.nr_in + spec.nr_steps; i++) {
            spec.nr_sel_vars += (i * (i - 1) * (i - 2)) / 6;
        }
        spec.sel_offset = 0;
        spec.steps_offset = spec.nr_sel_vars;
        spec.out_offset = spec.nr_sel_vars + spec.nr_op_vars;
        spec.sim_offset = spec.nr_sel_vars + spec.nr_op_vars + spec.nr_out_vars;
        spec.fence_offset = spec.nr_sel_vars + spec.nr_op_vars + 
            spec.nr_out_vars + spec.nr_sim_vars;

        solver_set_nr_vars(spec.solver(), spec.nr_op_vars + spec.nr_out_vars +
                spec.nr_sim_vars + spec.nr_sel_vars);
        
        // TODO: compute better upper bound on number of literals
        Vec_IntGrowResize(spec.vLits, spec.nr_sel_vars);
    }
    
    template<typename TT, typename Solver>
    bool add_simulation_clause(
            const synth_spec<TT,Solver>& spec, int i, int j, 
            int k, int t, int a, int b, int c)
    {
        int pLits[5], ctr = 0;

        if (j < spec.nr_in) {
            if (( ( ( t + 1 ) & ( 1 << j ) ) ? 1 : 0 ) != b) {
                return true;
            }
        } else {
            pLits[ctr++] = Abc_Var2Lit(get_sim_var(spec, j - spec.nr_in, t), b);
        }

        if (k < spec.nr_in) {
            if (( ( ( t + 1 ) & ( 1 << k ) ) ? 1 : 0 ) != c)
                return true;
        } else {
            pLits[ctr++] = Abc_Var2Lit(get_sim_var(spec, k - spec.nr_in, t), c);
        }

        /*
        printf("adding sim clause for s_%d_%d_%d, x_%d_%d, x_%d_%d, x_%d_%d\n",
                i+1, j+1, k+1, i+1, t+1, j+1, t+1, k+1, t+1);
        printf("!s_%d_%d_%d\n", i+1, j+1, k+1);
        printf("%sx_%d_%d\n", a ? "!" : "", i+1, t+1);
        */
        pLits[ctr++] = Abc_Var2Lit(get_sel_var(spec, i, j, k ), 1);
        pLits[ctr++] = Abc_Var2Lit(get_sim_var(spec, i, t), a);

        if (b | c) {
            pLits[ctr++] = Abc_Var2Lit(get_op_var(spec, i, c, b), 1 - a);
            //printf("%sf_%d_%d_%d\n", (1-a) ? "!" : "", i+1, c, b);
        }
        
        return solver_add_clause(spec.solver(), pLits, pLits + ctr);
    }

    template<typename TT, typename Solver>
    bool top_add_simulation_clause(
            const synth_spec<TT,Solver>& spec, int i, int j, 
            int k, int t, int a, int b, int c)
    {
        int pLits[5], ctr = 0;

        if (j < spec.nr_in) {
            if (( ( ( t + 1 ) & ( 1 << j ) ) ? 1 : 0 ) != b) {
                return true;
            }
        } else {
            pLits[ctr++] = Abc_Var2Lit(get_sim_var(spec, j - spec.nr_in, t), b);
        }

        if (k < spec.nr_in) {
            if (( ( ( t + 1 ) & ( 1 << k ) ) ? 1 : 0 ) != c)
                return true;
        } else {
            pLits[ctr++] = Abc_Var2Lit(get_sim_var(spec, k - spec.nr_in, t), c);
        }

        pLits[ctr++] = Abc_Var2Lit(spec.selection_vars[i][j][k], 1);
        pLits[ctr++] = Abc_Var2Lit(get_sim_var(spec, i, t), a);

        if (b | c) {
            pLits[ctr++] = Abc_Var2Lit(get_op_var(spec, i, c, b), 1 - a);
        }
        
        return solver_add_clause(spec.solver(), pLits, pLits + ctr);
    }

    template<typename TT, typename Solver>
    bool add_simulation_clause(
            const synth_spec<TT,Solver>& spec, int i, int j, 
            int k, int l, int t, int a, int b, int c, int d)
    {
        int pLits[6], ctr = 0;

        if (j < spec.nr_in) {
            if (( ( ( t + 1 ) & ( 1 << j ) ) ? 1 : 0 ) != b) {
                return true;
            }
        } else {
            pLits[ctr++] = Abc_Var2Lit(get_sim_var(spec, j - spec.nr_in, t), b);
        }

        if (k < spec.nr_in) {
            if (( ( ( t + 1 ) & ( 1 << k ) ) ? 1 : 0 ) != c)
                return true;
        } else {
            pLits[ctr++] = Abc_Var2Lit(get_sim_var(spec, k - spec.nr_in, t), c);
        }

        if (l < spec.nr_in) {
            if (( ( ( t + 1 ) & ( 1 << l ) ) ? 1 : 0 ) != d)
                return true;
        } else {
            pLits[ctr++] = Abc_Var2Lit(get_sim_var(spec, l - spec.nr_in, t), d);
        }

        pLits[ctr++] = Abc_Var2Lit(get_sel_var(spec, i, j, k, l), 1);
        pLits[ctr++] = Abc_Var2Lit(get_sim_var(spec, i, t), a);

        if (b | c | d) {
            pLits[ctr++] = Abc_Var2Lit(get_op_var(spec, i, d, c, b), 1 - a);
        }
        
        return solver_add_clause(spec.solver(), pLits, pLits + ctr);
    }

    
    template<typename TT, typename Solver>
    bool create_tt_clauses(const synth_spec<TT,Solver>& spec, int t)
    {
        int pLits[2];

        auto ret = true;

        for (int i = 0; i < spec.nr_steps; i++) {
            for (int k = 1; k < spec.nr_in + i; k++) {
                for (int j = 0; j < k; j++) {
                    ret &= add_simulation_clause(spec, i, j, k, t, 0, 0, 1);
                    ret &= add_simulation_clause(spec, i, j, k, t, 0, 1, 0);
                    ret &= add_simulation_clause(spec, i, j, k, t, 0, 1, 1);
                    ret &= add_simulation_clause(spec, i, j, k, t, 1, 0, 0);
                    ret &= add_simulation_clause(spec, i, j, k, t, 1, 0, 1);
                    ret &= add_simulation_clause(spec, i, j, k, t, 1, 1, 0);
                    ret &= add_simulation_clause(spec, i, j, k, t, 1, 1, 1);
                }
            }

            // If an output has selected this particular operand, we
            // need to ensure that this operand's truth table satisfies
            // the specified output function.
            for (int h = 0; h < spec.nr_nontriv; h++) {
                auto outbit = kitty::get_bit(
                        *spec.functions[spec.synth_functions[h]], t+1);
                if ((spec.out_inv >> spec.synth_functions[h]) & 1) {
                    outbit = 1 - outbit;
                }
                pLits[0] = Abc_Var2Lit(get_out_var(spec, h, i), 1);
                pLits[1] = Abc_Var2Lit(get_sim_var(spec, i, t), 
                        1 - outbit);
                ret &= solver_add_clause(spec.solver(),pLits,pLits+2);
                if (spec.verbosity > 1) {
                    printf("  (g_%d_%d --> %sx_%d_%d)\n", h+1, spec.nr_in+i+1,
                            (1 - outbit) ? 
                            "!" : "", spec.nr_in+i+1, t+1);
                }
            }
        }

        return ret;
    }

    template<typename TT, typename Solver>
    bool top_create_tt_clauses(const synth_spec<TT,Solver>& spec, int t)
    {
        int pLits[2];

        auto ret = true;

        
        for (int i = 0; i < spec.nr_steps; i++) {
            auto level = spec.get_level(i + spec.nr_in);
            assert(level > 0);
            for (auto k = spec.first_step_on_level(level-1); 
                    k < spec.first_step_on_level(level); k++) {
                for (int j = 0; j < k; j++) {
                    ret &= top_add_simulation_clause(spec, i, j, k, t, 0, 0, 1);
                    ret &= top_add_simulation_clause(spec, i, j, k, t, 0, 1, 0);
                    ret &= top_add_simulation_clause(spec, i, j, k, t, 0, 1, 1);
                    ret &= top_add_simulation_clause(spec, i, j, k, t, 1, 0, 0);
                    ret &= top_add_simulation_clause(spec, i, j, k, t, 1, 0, 1);
                    ret &= top_add_simulation_clause(spec, i, j, k, t, 1, 1, 0);
                    ret &= top_add_simulation_clause(spec, i, j, k, t, 1, 1, 1);
                }
            }

            // If an output has selected this particular operand, we
            // need to ensure that this operand's truth table satisfies
            // the specified output function.
            for (int h = 0; h < spec.nr_nontriv; h++) {
                auto outbit = kitty::get_bit(
                        *spec.functions[spec.synth_functions[h]], t+1);
                if ((spec.out_inv >> spec.synth_functions[h]) & 1) {
                    outbit = 1 - outbit;
                }
                pLits[0] = Abc_Var2Lit(get_out_var(spec, h, i), 1);
                pLits[1] = Abc_Var2Lit(get_sim_var(spec, i, t), 
                        1 - outbit);
                ret &= solver_add_clause(spec.solver(),pLits,pLits+2);
                if (spec.verbosity > 1) {
                    printf("  (g_%d_%d --> %sx_%d_%d)\n", h+1, spec.nr_in+i+1,
                            (1 - outbit) ? 
                            "!" : "", spec.nr_in+i+1, t+1);
                }
            }
        }

        return ret;
    }

    template<typename TT, typename Solver>
    bool create_tt_clauses3(const synth_spec<TT,Solver>& spec, int t)
    {
        int pLits[2];

        auto ret = true;

        for (int i = 0; i < spec.nr_steps; i++) {
            for (int l = 2; l < spec.nr_in + i; l++) {
                for (int k = 1; k < l; k++) {
                    for (int j = 0; j < k; j++) {
                        ret &= add_simulation_clause(spec, i, j, k, l, t, 0, 0, 0, 1);
                        ret &= add_simulation_clause(spec, i, j, k, l, t, 0, 0, 1, 0);
                        ret &= add_simulation_clause(spec, i, j, k, l, t, 0, 0, 1, 1);
                        ret &= add_simulation_clause(spec, i, j, k, l, t, 0, 1, 0, 0);
                        ret &= add_simulation_clause(spec, i, j, k, l, t, 0, 1, 0, 1);
                        ret &= add_simulation_clause(spec, i, j, k, l, t, 0, 1, 1, 0);
                        ret &= add_simulation_clause(spec, i, j, k, l, t, 0, 1, 1, 1);
                        ret &= add_simulation_clause(spec, i, j, k, l, t, 1, 0, 0, 0);
                        ret &= add_simulation_clause(spec, i, j, k, l, t, 1, 0, 0, 1);
                        ret &= add_simulation_clause(spec, i, j, k, l, t, 1, 0, 1, 0);
                        ret &= add_simulation_clause(spec, i, j, k, l, t, 1, 0, 1, 1);
                        ret &= add_simulation_clause(spec, i, j, k, l, t, 1, 1, 0, 0);
                        ret &= add_simulation_clause(spec, i, j, k, l, t, 1, 1, 0, 1);
                        ret &= add_simulation_clause(spec, i, j, k, l, t, 1, 1, 1, 0);
                        ret &= add_simulation_clause(spec, i, j, k, l, t, 1, 1, 1, 1);
                    }
                }
            }
            // If an output has selected this particular operand, we
            // need to ensure that this operand's truth table satisfies
            // the specified output function.
            for (int h = 0; h < spec.nr_nontriv; h++) {
                auto outbit = kitty::get_bit(
                        *spec.functions[spec.synth_functions[h]], t+1);
                if ((spec.out_inv >> spec.synth_functions[h]) & 1) {
                    outbit = 1 - outbit;
                }
                pLits[0] = Abc_Var2Lit(get_out_var(spec, h, i), 1);
                pLits[1] = Abc_Var2Lit(get_sim_var(spec, i, t), 
                        1 - outbit);
                ret &= solver_add_clause(spec.solver(),pLits,pLits+2);
                if (spec.verbosity > 1) {
                    printf("  (g_%d_%d --> %sx_%d_%d)\n", h+1, spec.nr_in+i+1,
                            (1 - outbit) ? 
                            "!" : "", spec.nr_in+i+1, t+1);
                }
            }
        }

        return ret;
    }

    template<typename TT, typename Solver>
    void create_main_clauses(const synth_spec<TT,Solver>& spec)
    {
        for (int t = 0; t < spec.tt_size; t++) {
            create_tt_clauses(spec, t);
        }
    }

    template<typename TT, typename Solver>
    void top_create_main_clauses(const synth_spec<TT,Solver>& spec)
    {
        for (int t = 0; t < spec.tt_size; t++) {
            top_create_tt_clauses(spec, t);
        }
    }

    template<typename TT, typename Solver>
    void create_main_clauses3(const synth_spec<TT,Solver>& spec)
    {
        for (int t = 0; t < spec.tt_size; t++) {
            create_tt_clauses3(spec, t);
        }
    }

    template<typename TT, typename Solver>
    void 
    create_output_clauses(const synth_spec<TT,Solver>& spec)
    {
        // Every output points to an operand.
        if (spec.nr_nontriv > 1) {
            for (int h = 0; h < spec.nr_nontriv; h++) {
                for (int i = 0; i < spec.nr_steps; i++) {
                    Vec_IntSetEntry(spec.vLits, i, 
                            Abc_Var2Lit(get_out_var(spec, h, i), 0));
                    if (spec.verbosity) {
                        printf("  output %d may point to step %d\n", 
                                h+1, spec.nr_in+i+1);
                    }
                }
                solver_add_clause(spec.solver(), Vec_IntArray(spec.vLits), 
                        Vec_IntArray(spec.vLits) + spec.nr_steps);
            }
        }
        
        // At least one of the outputs has to refer to the final operator,
        // otherwise it may as well not be there.
        const auto last_op = spec.nr_steps - 1;
        for (int h = 0; h < spec.nr_nontriv; h++) {
            Vec_IntSetEntry(spec.vLits, h, 
                    Abc_Var2Lit(get_out_var(spec, h, last_op), 0));
        }
        solver_add_clause(spec.solver(), Vec_IntArray(spec.vLits), 
                Vec_IntArray(spec.vLits) + spec.nr_nontriv);
    }

    /***************************************************************************
        Ensures that each gate has two operands.
    ***************************************************************************/
    template<typename TT, typename Solver>
    void 
    create_op_clauses(const synth_spec<TT,Solver>& spec)
    {
        for (int i = 0; i < spec.nr_steps; i++)
        {
            int ctr = 0;
            for (int k = 1; k < spec.nr_in + i; k++) {
                for (int j = 0; j < k; j++) {
                    Vec_IntSetEntry(spec.vLits, ctr++, 
                            Abc_Var2Lit(get_sel_var(spec, i, j, k ), 0 ));
                }
            }
            solver_add_clause(spec.solver(), Vec_IntArray(spec.vLits), 
                    Vec_IntArray(spec.vLits) + ctr);
        }
    }

    template<typename TT, typename Solver>
    void 
    top_create_op_clauses(const synth_spec<TT,Solver>& spec)
    {
        for (int i = 0; i < spec.nr_steps; i++)
        {
            auto level = spec.get_level(i + spec.nr_in);
            assert(level > 0);
            int ctr = 0;
            for (auto k = spec.first_step_on_level(level-1); 
                    k < spec.first_step_on_level(level); k++) {
                for (int j = 0; j < k; j++) {
                    Vec_IntSetEntry(spec.vLits, ctr++, 
                            Abc_Var2Lit(spec.selection_vars[i][j][k], 0));
                }
            }
            solver_add_clause(spec.solver(), Vec_IntArray(spec.vLits), 
                    Vec_IntArray(spec.vLits) + ctr);
        }
    }

    template<typename TT, typename Solver>
    void 
    create_op_clauses3(const synth_spec<TT,Solver>& spec)
    {
        for (int i = 0; i < spec.nr_steps; i++)
        {
            int ctr = 0;
            for (int l = 2; l < spec.nr_in + i; l++) {
                for (int k = 1; k < l; k++) {
                    for (int j = 0; j < k; j++) {
                        Vec_IntSetEntry(spec.vLits, ctr++, 
                                Abc_Var2Lit(get_sel_var(spec, i, j, k, l), 0 ));
                    }
                }
            }
            solver_add_clause(spec.solver(), Vec_IntArray(spec.vLits), 
                    Vec_IntArray(spec.vLits) + ctr);
        }
    }

    /***************************************************************************
        Add clauses that prevent trivial variable projection and constant
        operators from being synthesized.
    ***************************************************************************/
    template<typename TT, typename Solver>
    void create_nontriv_clauses(const synth_spec<TT,Solver>& spec)
    {
        int pLits[3];

        for (int i = 0; i < spec.nr_steps; i++) {
            pLits[0] = Abc_Var2Lit(get_op_var(spec, i, 0, 1), 0);
            pLits[1] = Abc_Var2Lit(get_op_var(spec, i, 1, 0), 0);
            pLits[2] = Abc_Var2Lit(get_op_var(spec, i, 1, 1), 0);
            solver_add_clause(spec.solver(), pLits, pLits + 3);

            pLits[0] = Abc_Var2Lit(get_op_var(spec, i, 0, 1), 0);
            pLits[1] = Abc_Var2Lit(get_op_var(spec, i, 1, 0), 1);
            pLits[2] = Abc_Var2Lit(get_op_var(spec, i, 1, 1), 1);
            solver_add_clause(spec.solver(), pLits, pLits + 3);
            
            pLits[0] = Abc_Var2Lit(get_op_var(spec, i, 0, 1), 1);
            pLits[1] = Abc_Var2Lit(get_op_var(spec, i, 1, 0), 0);
            pLits[2] = Abc_Var2Lit(get_op_var(spec, i, 1, 1), 1);
            solver_add_clause(spec.solver(), pLits, pLits + 3);
        }
    }

    template<typename TT, typename Solver>
    void create_nontriv_clauses3(const synth_spec<TT,Solver>& spec)
    {
        int pLits[7];

        for (int i = 0; i < spec.nr_steps; i++) {
            pLits[0] = Abc_Var2Lit(get_op_var(spec, i, 0, 0, 1), 0);
            pLits[1] = Abc_Var2Lit(get_op_var(spec, i, 0, 1, 0), 0);
            pLits[2] = Abc_Var2Lit(get_op_var(spec, i, 0, 1, 1), 0);
            pLits[3] = Abc_Var2Lit(get_op_var(spec, i, 1, 0, 0), 0);
            pLits[4] = Abc_Var2Lit(get_op_var(spec, i, 1, 0, 1), 0);
            pLits[5] = Abc_Var2Lit(get_op_var(spec, i, 1, 1, 0), 0);
            pLits[6] = Abc_Var2Lit(get_op_var(spec, i, 1, 1, 1), 0);
            solver_add_clause(spec.solver(), pLits, pLits + 7);


            pLits[0] = Abc_Var2Lit(get_op_var(spec, i, 0, 0, 1), 0);
            pLits[1] = Abc_Var2Lit(get_op_var(spec, i, 0, 1, 0), 1);
            pLits[2] = Abc_Var2Lit(get_op_var(spec, i, 0, 1, 1), 1);
            pLits[3] = Abc_Var2Lit(get_op_var(spec, i, 1, 0, 0), 0);
            pLits[4] = Abc_Var2Lit(get_op_var(spec, i, 1, 0, 1), 0);
            pLits[5] = Abc_Var2Lit(get_op_var(spec, i, 1, 1, 0), 1);
            pLits[6] = Abc_Var2Lit(get_op_var(spec, i, 1, 1, 1), 1);
            solver_add_clause(spec.solver(), pLits, pLits + 7);
            
            pLits[0] = Abc_Var2Lit(get_op_var(spec, i, 0, 0, 1), 1);
            pLits[1] = Abc_Var2Lit(get_op_var(spec, i, 0, 1, 0), 0);
            pLits[2] = Abc_Var2Lit(get_op_var(spec, i, 0, 1, 1), 1);
            pLits[3] = Abc_Var2Lit(get_op_var(spec, i, 1, 0, 0), 0);
            pLits[4] = Abc_Var2Lit(get_op_var(spec, i, 1, 0, 1), 1);
            pLits[5] = Abc_Var2Lit(get_op_var(spec, i, 1, 1, 0), 0);
            pLits[6] = Abc_Var2Lit(get_op_var(spec, i, 1, 1, 1), 1);
            solver_add_clause(spec.solver(), pLits, pLits + 7);

            pLits[0] = Abc_Var2Lit(get_op_var(spec, i, 0, 0, 1), 0);
            pLits[1] = Abc_Var2Lit(get_op_var(spec, i, 0, 1, 0), 0);
            pLits[2] = Abc_Var2Lit(get_op_var(spec, i, 0, 1, 1), 0);
            pLits[3] = Abc_Var2Lit(get_op_var(spec, i, 1, 0, 0), 1);
            pLits[4] = Abc_Var2Lit(get_op_var(spec, i, 1, 0, 1), 1);
            pLits[5] = Abc_Var2Lit(get_op_var(spec, i, 1, 1, 0), 1);
            pLits[6] = Abc_Var2Lit(get_op_var(spec, i, 1, 1, 1), 1);
            solver_add_clause(spec.solver(), pLits, pLits + 7);
        }
    }

    /***************************************************************************
        Add clauses which ensure that every step is used at least once.
    ***************************************************************************/
    template<typename TT, typename Solver>
    void 
    create_alonce_clauses(const synth_spec<TT,Solver>& spec)
    {
        for (int i = 0; i < spec.nr_steps; i++) {
            auto ctr = 0;
            for (int h = 0; h < spec.nr_nontriv; h++) {
                Vec_IntSetEntry(spec.vLits, ctr++, 
                        Abc_Var2Lit(get_out_var(spec, h, i), 0));
            }
            for (int ip = i + 1; ip < spec.nr_steps; ip++) {
                for (int j = 0; j < spec.nr_in+i; j++) {
                    Vec_IntSetEntry(spec.vLits, ctr++, Abc_Var2Lit(
                                get_sel_var(spec, ip, j, spec.nr_in+i), 0));
                }
                for (int j = spec.nr_in+i+1; j < spec.nr_in+ip; j++) {
                    Vec_IntSetEntry(spec.vLits, ctr++, Abc_Var2Lit(
                                get_sel_var(spec, ip, spec.nr_in+i, j), 0));
                }
            }
            solver_add_clause(spec.solver(), Vec_IntArray(spec.vLits),
                    Vec_IntArray(spec.vLits) + ctr);
        }
    }

    template<typename TT, typename Solver>
    void 
    top_create_alonce_clauses(const synth_spec<TT,Solver>& spec)
    {
        for (int i = 0; i < spec.nr_steps; i++) {
            auto ctr = 0;
            for (int h = 0; h < spec.nr_nontriv; h++) {
                Vec_IntSetEntry(spec.vLits, ctr++, 
                        Abc_Var2Lit(get_out_var(spec, h, i), 0));
            }
            const auto level = spec.get_level(i + spec.nr_in);
            const auto idx = spec.nr_in+i;
            for (int ip = i + 1; ip < spec.nr_steps; ip++) {
                auto levelp = spec.get_level(ip + spec.nr_in);
                assert(levelp >= level);
                if (levelp == level) {
                    continue;
                }
                for (auto k = spec.first_step_on_level(levelp-1); 
                        k < spec.first_step_on_level(levelp); k++) {
                    for (int j = 0; j < k; j++) {
                        if (j == idx || k == idx) {
                            Vec_IntSetEntry(spec.vLits, ctr++, Abc_Var2Lit(
                                    spec.selection_vars[ip][j][k], 0));
                        }
                    }
                }
            }
            solver_add_clause(spec.solver(), Vec_IntArray(spec.vLits),
                    Vec_IntArray(spec.vLits) + ctr);
        }
    }

    template<typename TT, typename Solver>
    void 
    create_alonce_clauses3(const synth_spec<TT,Solver>& spec)
    {
        for (int i = 0; i < spec.nr_steps; i++) {
            auto ctr = 0;
            for (int h = 0; h < spec.nr_nontriv; h++) {
                Vec_IntSetEntry(spec.vLits, ctr++, 
                        Abc_Var2Lit(get_out_var(spec, h, i), 0));
            }
            for (int ip = i + 1; ip < spec.nr_steps; ip++) {
                for (int k = 1; k < spec.nr_in+i; k++) {
                    for (int j = 0; j < k; j++) {
                        Vec_IntSetEntry(spec.vLits, ctr++, Abc_Var2Lit(
                                    get_sel_var(spec, ip, j, k, spec.nr_in+i),
                                    0));
                    }
                }
                for (int k = spec.nr_in+i+2; k < spec.nr_in+ip; k++) {
                    for (int j = spec.nr_in+i+1; j < k; j++) {
                        Vec_IntSetEntry(spec.vLits, ctr++, Abc_Var2Lit(
                                    get_sel_var(spec, ip, spec.nr_in+i, j, k),
                                    0)); 
                    }
                }
            }
            solver_add_clause(spec.solver(), Vec_IntArray(spec.vLits),
                    Vec_IntArray(spec.vLits) + ctr);
        }
    }
    
    /***************************************************************************
        Add clauses which ensure that operands are never re-applied. In other
        words, (Sijk --> ~Si'ji) & (Sijk --> ~Si'ki), for all (i < i').
    ***************************************************************************/
    template<typename TT, typename Solver>
    void create_noreapply_clauses(const synth_spec<TT,Solver>& spec)
    {
        int pLits[2];

        for (int i = 0; i < spec.nr_steps; i++) {
            for (int ip = i+1; ip < spec.nr_steps; ip++) {
                for (int k = 1; k < spec.nr_in+i; k++) {
                    for (int j = 0; j < k; j++) {
                        pLits[0] = Abc_Var2Lit(
                                get_sel_var(spec, i, j, k), 1);
                        pLits[1] = Abc_Var2Lit(
                                get_sel_var(spec, ip, j, spec.nr_in+i), 1);
                        solver_add_clause(spec.solver(), pLits, pLits+2);
                        pLits[1] = Abc_Var2Lit(
                                get_sel_var(spec, ip, k, spec.nr_in+i), 1);
                        solver_add_clause(spec.solver(), pLits, pLits+2);
                    }
                }
            }
        }
    }


    template<typename TT, typename Solver>
    void top_create_noreapply_clauses(const synth_spec<TT,Solver>& spec)
    {
        int pLits[2];

        for (int i = 0; i < spec.nr_steps; i++) {
            const auto level = spec.get_level(i + spec.nr_in);
            const auto idx = spec.nr_in+i;

            for (int ip = i+1; ip < spec.nr_steps; ip++) {
                const auto levelp = spec.get_level(ip + spec.nr_in);
                if (levelp == level) { 
                    // A node cannot have a node on the same level in its
                    // fanin.
                    continue;
                }

                for (auto k = spec.first_step_on_level(level-1); 
                        k < spec.first_step_on_level(level); k++) {
                    for (int j = 0; j < k; j++) {
                        pLits[0] = Abc_Var2Lit(
                                spec.selection_vars[i][j][k], 1);

                        // Note that it's possible for node ip to never have
                        // i as its second fanin.
                        for (auto kp = spec.first_step_on_level(levelp-1); 
                                kp < spec.first_step_on_level(levelp); kp++) {
                            if (kp == idx) {
                                pLits[1] = Abc_Var2Lit(
                                        spec.selection_vars[ip][j][kp], 1);
                                solver_add_clause(spec.solver(), pLits, pLits+2);
                                pLits[1] = Abc_Var2Lit(
                                        spec.selection_vars[ip][k][kp], 1);
                                solver_add_clause(spec.solver(), pLits, pLits+2);
                            }
                        }
                    }
                }
            }
        }
    }

    template<typename TT, typename Solver>
    void create_noreapply_clauses3(const synth_spec<TT,Solver>& spec)
    {
        int pLits[2];

        for (int i = 0; i < spec.nr_steps; i++) {
            for (int ip = i+1; ip < spec.nr_steps; ip++) {
                for (int l = 2; l < spec.nr_in+i; l++) {
                    for (int k = 1; k < l; k++) {
                        for (int j = 0; j < k; j++) {
                            pLits[0] = Abc_Var2Lit(
                                    get_sel_var(spec, i, j, k, l), 1);
                            pLits[1] = Abc_Var2Lit(
                                    get_sel_var(spec, ip, j, k, spec.nr_in+i), 1);
                            solver_add_clause(spec.solver(), pLits, pLits+2);
                            pLits[1] = Abc_Var2Lit(
                                    get_sel_var(spec, ip, j, l, spec.nr_in+i), 1);
                            solver_add_clause(spec.solver(), pLits, pLits+2);
                            pLits[1] = Abc_Var2Lit(
                                    get_sel_var(spec, ip, k, l, spec.nr_in+i), 1);
                            solver_add_clause(spec.solver(), pLits, pLits+2);
                        }
                    }
                }
            }
        }
    }

    /***************************************************************************
        Add clauses which ensure that steps occur in co-lexicographic order. In
        other words, we require steps operands to be ordered tuples.
    ***************************************************************************/
    template<typename TT, typename Solver>
    void create_colex_clauses(const synth_spec<TT,Solver>& spec)
    {
        int pLits[2];

        for (int i = 0; i < spec.nr_steps-1; i++) {
            for (int k = 2; k < spec.nr_in+i; k++) {
                for (int j = 1; j < k; j++) {
                    for (int jp = 0; jp < j; jp++) {
                        pLits[0] = Abc_Var2Lit(get_sel_var(spec, i, j, k), 1);
                        pLits[1] = Abc_Var2Lit(
                                get_sel_var(spec, i+1, jp, k), 1);
                        solver_add_clause(spec.solver(), pLits, pLits+2);
                    }
                }
                for (int j = 0; j < k; j++) {
                    for (int kp = 1; kp < k; kp++) {
                        for (int jp = 0; jp < kp; jp++) {
                            pLits[0] = Abc_Var2Lit(
                                    get_sel_var(spec, i, j, k), 1);
                            pLits[1] = Abc_Var2Lit(
                                    get_sel_var(spec, i+1, jp, kp),1);
                            solver_add_clause(spec.solver(), pLits, pLits+2);
                        }
                    }
                }
            }
        }
    }

    template<typename TT, typename Solver>
    void top_create_colex_clauses(const synth_spec<TT,Solver>& spec)
    {
        int pLits[2];

        for (int i = 0; i < spec.nr_steps-1; i++) {
            const auto level = spec.get_level(i + spec.nr_in);
            const auto levelp = spec.get_level(i + 1 + spec.nr_in);
            for (auto k = spec.first_step_on_level(level-1); 
                    k < spec.first_step_on_level(level); k++) {
                if (k < 2) continue;
                for (auto kp = spec.first_step_on_level(levelp-1); 
                        kp < spec.first_step_on_level(levelp); kp++) {
                    if (kp != k) {
                        continue;
                    }
                    for (int j = 1; j < k; j++) {
                        for (int jp = 0; jp < j; jp++) {
                            pLits[0] = Abc_Var2Lit(spec.selection_vars[i][j][k], 1);
                            pLits[1] = Abc_Var2Lit(
                                    spec.selection_vars[i+1][jp][k], 1);
                            solver_add_clause(spec.solver(), pLits, pLits+2);
                        }
                    }
                }
                const auto min_kp = spec.first_step_on_level(levelp-1);
                const auto max_kp = spec.first_step_on_level(levelp);
                for (int j = 0; j < k; j++) {
                    for (int kp = 1; kp < k; kp++) {
                        if (kp < min_kp || kp >= max_kp) {
                            // Node ip would never select these j and kp
                            // anyway.
                            continue;
                        }
                        for (int jp = 0; jp < kp; jp++) {
                            pLits[0] = Abc_Var2Lit(
                                    spec.selection_vars[i][j][k], 1);
                            pLits[1] = Abc_Var2Lit(
                                    spec.selection_vars[i+1][jp][kp],1);
                            solver_add_clause(spec.solver(), pLits, pLits+2);
                        }
                    }
                }
            }
        }
    }

    template<typename TT, typename Solver>
    void create_colex_clauses3(const synth_spec<TT,Solver>& spec)
    {
        int pLits[2];

        for (int i = 0; i < spec.nr_steps-1; i++) {
            for (int l = 3; l < spec.nr_in+i; l++) {
                for (int k = 2; k < l; k++) {
                    for (int j = 1; j < k; j++) {
                        for (int jp = 0; jp < j; jp++) {
                            pLits[0] = Abc_Var2Lit(
                                    get_sel_var(spec, i, j, k, l), 1);
                            pLits[1] = Abc_Var2Lit(
                                    get_sel_var(spec, i+1, jp, k, l), 1);
                            solver_add_clause(spec.solver(), pLits, pLits+2);
                        }
                        for (int kp = 1; kp < k; kp++) {
                            for (int jp = 0; jp < kp; jp++) {
                                pLits[0] = Abc_Var2Lit(
                                        get_sel_var(spec, i, j, k, l), 1);
                                pLits[1] = Abc_Var2Lit(
                                        get_sel_var(spec, i+1, jp, kp, l), 1);
                                solver_add_clause(spec.solver(), pLits, pLits+2);
                            }
                        }
                    }
                    for (int j = 0; j < k; j++) {
                        for (int lp = 2; lp < l; lp++) {
                            for (int kp = 1; kp < lp; kp++) {
                                for (int jp = 0; jp < kp; jp++) {
                                    pLits[0] = Abc_Var2Lit(
                                            get_sel_var(spec, i, j, k, l), 1);
                                    pLits[1] = Abc_Var2Lit(
                                            get_sel_var(spec, i+1, jp, kp, lp),1);
                                    solver_add_clause(spec.solver(), pLits, pLits+2);
                                }
                            }
                        }
                    }
                }
            }
        }
    }
    
    /***************************************************************************
        Ensure that Boolean operators are co-lexicographically ordered:
                    (S_ijk == S_(i+1)jk) ==> f_i <= f_(i+1)
    ***************************************************************************/
    template<typename TT, typename Solver>
    void create_colex_func_clauses(const synth_spec<TT,Solver>& spec)
    {
        int pLits[6];

        for (int i = 0; i < spec.nr_steps-1; i++) {
            for (int k = 1; k < spec.nr_in+i; k++) {
                for (int j = 0; j < k; j++) {
                    pLits[0] = Abc_Var2Lit(get_sel_var(spec, i, j, k), 1);
                    pLits[1] = Abc_Var2Lit(get_sel_var(spec, i+1, j, k), 1);

                    pLits[2] = Abc_Var2Lit(get_op_var(spec, i, 1, 1), 1);
                    pLits[3] = Abc_Var2Lit(get_op_var(spec, i+1, 1, 1), 0);
                    solver_add_clause(spec.solver(), pLits, pLits+4);

                    pLits[3] = Abc_Var2Lit(get_op_var(spec, i, 1, 0), 1);
                    pLits[4] = Abc_Var2Lit(get_op_var(spec, i+1, 1, 1), 0);
                    solver_add_clause(spec.solver(), pLits, pLits+5);
                    pLits[4] = Abc_Var2Lit(get_op_var(spec, i+1, 1, 0), 0);
                    solver_add_clause(spec.solver(), pLits, pLits+5);
                    
                    pLits[4] = Abc_Var2Lit(get_op_var(spec, i, 0, 1), 1);
                    pLits[5] = Abc_Var2Lit(get_op_var(spec, i+1, 1, 1), 0);
                    solver_add_clause(spec.solver(), pLits, pLits+6);
                    pLits[5] = Abc_Var2Lit(get_op_var(spec, i+1, 1, 0), 0);
                    solver_add_clause(spec.solver(), pLits, pLits+6);
                    pLits[5] = Abc_Var2Lit(get_op_var(spec, i+1, 0, 1), 0);
                    solver_add_clause(spec.solver(), pLits, pLits+6);
                }
            }
        }
    }

    template<typename TT, typename Solver>
    void top_create_colex_func_clauses(const synth_spec<TT,Solver>& spec)
    {
        int pLits[6];

        for (int i = 0; i < spec.nr_steps-1; i++) {
            for (int k = 1; k < spec.nr_in+i; k++) {
                for (int j = 0; j < k; j++) {
                    pLits[0] = Abc_Var2Lit(spec.selection_vars[i][j][k], 1);
                    pLits[1] = Abc_Var2Lit(spec.selection_vars[i+1][j][k], 1);

                    pLits[2] = Abc_Var2Lit(get_op_var(spec, i, 1, 1), 1);
                    pLits[3] = Abc_Var2Lit(get_op_var(spec, i+1, 1, 1), 0);
                    solver_add_clause(spec.solver(), pLits, pLits+4);

                    pLits[3] = Abc_Var2Lit(get_op_var(spec, i, 1, 0), 1);
                    pLits[4] = Abc_Var2Lit(get_op_var(spec, i+1, 1, 1), 0);
                    solver_add_clause(spec.solver(), pLits, pLits+5);
                    pLits[4] = Abc_Var2Lit(get_op_var(spec, i+1, 1, 0), 0);
                    solver_add_clause(spec.solver(), pLits, pLits+5);
                    
                    pLits[4] = Abc_Var2Lit(get_op_var(spec, i, 0, 1), 1);
                    pLits[5] = Abc_Var2Lit(get_op_var(spec, i+1, 1, 1), 0);
                    solver_add_clause(spec.solver(), pLits, pLits+6);
                    pLits[5] = Abc_Var2Lit(get_op_var(spec, i+1, 1, 0), 0);
                    solver_add_clause(spec.solver(), pLits, pLits+6);
                    pLits[5] = Abc_Var2Lit(get_op_var(spec, i+1, 0, 1), 0);
                    solver_add_clause(spec.solver(), pLits, pLits+6);
                }
            }
        }
    }

    /***************************************************************************
        Ensure that symmetric variables occur in order.
    ***************************************************************************/
    template<typename TT, typename Solver>
    void 
    create_symvar_clauses(const synth_spec<TT,Solver>& spec)
    {
        for (int q = 1; q < spec.nr_in; q++) {
            for (int p = 0; p < q; p++) {
                auto symm = true;
                for (int i = 0; i < spec.nr_out; i++) {
                    auto outfunc = spec.functions[i];
                    if (!(swap(*outfunc, p, q) == *outfunc)) {
                        symm = false;
                        break;
                    }
                }
                if (!symm) {
                    continue;
                }
                if (spec.verbosity) {
                    printf("  variables x_%d and x_%d are symmetric\n",
                            p+1, q+1);
                }
                for (int i = 0; i < spec.nr_steps; i++) {
                    for (int j = 0; j < q; j++) {
                        if (j == p) continue;

                        auto slit = Abc_Var2Lit(get_sel_var(spec, i, j, q), 1);
                        Vec_IntSetEntry(spec.vLits, 0, slit);
                        
                        int ctr = 1;
                        for (int ip = 0; ip < i; ip++) {
                            for (int kp = 1; kp < spec.nr_in + ip; kp++) {
                                for (int jp = 0; jp < kp; jp++) {
                                    if (jp == p || kp == p) {
                                        slit = Abc_Var2Lit(get_sel_var(spec, 
                                                    ip, jp, kp), 0);
                                        Vec_IntSetEntry(spec.vLits, ctr++, slit);
                                        solver_add_clause(spec.solver(), 
                                                Vec_IntArray(spec.vLits), 
                                                Vec_IntArray(spec.vLits) + ctr);
                                    }
                                }
                            }
                        }
                    }
                }
            }
        }
    }

    template<typename TT, typename Solver>
    void 
    top_create_symvar_clauses(const synth_spec<TT,Solver>& spec)
    {
        for (int q = 1; q < spec.nr_in; q++) {
            for (int p = 0; p < q; p++) {
                auto symm = true;
                for (int i = 0; i < spec.nr_out; i++) {
                    auto outfunc = spec.functions[i];
                    if (!(swap(*outfunc, p, q) == *outfunc)) {
                        symm = false;
                        break;
                    }
                }
                if (!symm) {
                    continue;
                }
                if (spec.verbosity) {
                    printf("  variables x_%d and x_%d are symmetric\n",
                            p+1, q+1);
                }
                for (int i = 0; i < spec.nr_steps; i++) {
                    const auto level = spec.get_level(i+spec.nr_in);
                    if (level > 1) {
                        // Any node on level 2 or higher could never refer to
                        // variable q as its second input.
                        continue;
                    }
                    for (int j = 0; j < q; j++) {
                        if (j == p) continue;

                        auto slit = Abc_Var2Lit(spec.selection_vars[i][j][q], 1);
                        Vec_IntSetEntry(spec.vLits, 0, slit);
                        
                        int ctr = 1;
                        for (int ip = 0; ip < i; ip++) {
                            const auto levelp = spec.get_level(ip+spec.nr_in);
                            for (auto kp = spec.first_step_on_level(levelp-1); 
                                    kp < spec.first_step_on_level(levelp); kp++) {
                                for (int jp = 0; jp < kp; jp++) {
                                    if (jp == p || kp == p) {
                                        slit = Abc_Var2Lit(
                                                spec.selection_vars[ip][jp][kp], 0);
                                        Vec_IntSetEntry(spec.vLits, ctr++, slit);
                                        solver_add_clause(spec.solver(), 
                                                Vec_IntArray(spec.vLits), 
                                                Vec_IntArray(spec.vLits) + ctr);
                                    }
                                }
                            }
                        }
                    }
                }
            }
        }
    }

    /***************************************************************************
        Ensure that steps obey the specified (partial) DAG topology. Each step
        must refer to at least one of the steps on the level below it.
    ***************************************************************************/
    template<typename TT, typename Solver>
    void 
    create_topology_clauses3(const synth_spec<TT,Solver>& spec)
    {
        for (int i = 1; i < spec.nr_steps; i++) {
            auto ctr = 0;
            // Determine the level of this step.
            auto level = spec.get_level(i + spec.nr_in);
            assert(level > 0);
            if (spec.verbosity) {
                printf("  step x_%d has level %d\n", spec.nr_in+i+1, level);
            }
            
            for (auto l = spec.first_step_on_level(level-1); 
                    l < spec.first_step_on_level(level); l++) {
                for (int k = 1; k < l; k++) {
                    for (int j = 0; j < k; j++) {
                        Vec_IntSetEntry(spec.vLits, ctr++, Abc_Var2Lit(
                                    get_sel_var(spec, i, j, k, l), 0));
                    }
                }
            }
            solver_add_clause(spec.solver(), Vec_IntArray(spec.vLits),
                    Vec_IntArray(spec.vLits) + ctr);
        }
    }

    /***************************************************************************
        Implements a simple SAT based exact synthesis algorithm. Uses only the
        bare minimum constraints necessary for the synthesis to be correct.
    ***************************************************************************/
    template<typename TT, typename Solver, int OpSize=2>
    class simple_synthesizer
    {
        public:
            void add_clauses(synth_spec<TT,Solver>& spec)
            {
                create_variables(spec);
                create_main_clauses(spec);
                create_output_clauses(spec);
                create_op_clauses(spec);
            }

            void add_clauses3(synth_spec<TT,Solver>& spec)
            {
                create_variables3(spec);
                create_main_clauses3(spec);
                create_output_clauses(spec);
                create_op_clauses3(spec);
            }

            void cegar_add_clauses(synth_spec<TT,Solver>& spec)
            {
                create_variables(spec);
                create_output_clauses(spec);
                create_op_clauses(spec);
            }

            void cegar_add_clauses3(synth_spec<TT,Solver>& spec)
            {
                create_variables3(spec);
                create_output_clauses(spec);
                create_op_clauses3(spec);
            }

            synth_result synthesize(synth_spec<TT,Solver>& spec, chain<TT,OpSize>& chain)
            {
                return std_synthesize(this, spec, chain);
            }

            synth_result synthesize3(synth_spec<TT,Solver>& spec, chain<TT,OpSize>& chain)
            {
                return std_synthesize3(this, spec, chain);
            }
            
            synth_result cegar_synthesize(synth_spec<TT,Solver>& spec, chain<TT,OpSize>& chain)
            {
                return cegar_std_synthesize(this, spec, chain);
            }
            
            synth_result cegar_synthesize3(synth_spec<TT,Solver>& spec, chain<TT,OpSize>& chain)
            {
                return cegar_std_synthesize3(this, spec, chain);
            }
    };

    /***************************************************************************
        This synthesizer adds clauses that prevent the synthesis of trivial
        operators. Note that this doesn't hurt our implementation, since we
        already detect and remove trivial functions from the synthesis spec.
    ***************************************************************************/
    template<typename TT, typename Solver, int OpSize=2>
    class nontriv_synthesizer
    {
        public:
            void add_clauses(synth_spec<TT,Solver>& spec)
            {
                create_variables(spec);
                create_main_clauses(spec);
                create_output_clauses(spec);
                create_op_clauses(spec);
                create_nontriv_clauses(spec);
            }

            void add_clauses3(synth_spec<TT,Solver>& spec)
            {
                create_variables3(spec);
                create_main_clauses3(spec);
                create_output_clauses(spec);
                create_op_clauses3(spec);
                create_nontriv_clauses3(spec);
            }
            
            void cegar_add_clauses(synth_spec<TT,Solver>& spec)
            {
                create_variables(spec);
                create_output_clauses(spec);
                create_op_clauses(spec);
                create_nontriv_clauses(spec);
            }

            void cegar_add_clauses3(synth_spec<TT,Solver>& spec)
            {
                create_variables3(spec);
                create_output_clauses(spec);
                create_op_clauses3(spec);
                create_nontriv_clauses3(spec);
            }

            synth_result synthesize(synth_spec<TT,Solver>& spec, chain<TT,OpSize>& chain)
            {
                return std_synthesize(this, spec, chain);
            }
            
            synth_result synthesize3(synth_spec<TT,Solver>& spec, chain<TT,OpSize>& chain)
            {
                return std_synthesize3(this, spec, chain);
            }
            
            synth_result cegar_synthesize(synth_spec<TT,Solver>& spec, chain<TT,OpSize>& chain)
            {
                return cegar_std_synthesize(this, spec, chain);
            }
            
            synth_result cegar_synthesize3(synth_spec<TT,Solver>& spec, chain<TT,OpSize>& chain)
            {
                return cegar_std_synthesize3(this, spec, chain);
            }
    };

    /***************************************************************************
        This synthesizer extends the nontriv_synthesizer and adds clauses which
        ensure that every step is used at least once.
    ***************************************************************************/
    template<typename TT, typename Solver, int OpSize=2>
    class alonce_synthesizer
    {
        public:
            void add_clauses(synth_spec<TT,Solver>& spec)
            {
                create_variables(spec);
                create_main_clauses(spec);
                create_output_clauses(spec);
                create_op_clauses(spec);
                create_nontriv_clauses(spec);
                create_alonce_clauses(spec);
            }

            void add_clauses3(synth_spec<TT,Solver>& spec)
            {
                create_variables3(spec);
                create_main_clauses3(spec);
                create_output_clauses(spec);
                create_op_clauses3(spec);
                create_nontriv_clauses3(spec);
                create_alonce_clauses3(spec);
            }

            void cegar_add_clauses(synth_spec<TT,Solver>& spec)
            {
                create_variables(spec);
                create_output_clauses(spec);
                create_op_clauses(spec);
                create_nontriv_clauses(spec);
                create_alonce_clauses(spec);
            }

            void cegar_add_clauses3(synth_spec<TT,Solver>& spec)
            {
                create_variables3(spec);
                create_output_clauses(spec);
                create_op_clauses3(spec);
                create_nontriv_clauses3(spec);
                create_alonce_clauses3(spec);
            }

            synth_result synthesize(synth_spec<TT,Solver>& spec, chain<TT,OpSize>& chain)
            {
                return std_synthesize(this, spec, chain);
            }
            
            synth_result synthesize3(synth_spec<TT,Solver>& spec, chain<TT,OpSize>& chain)
            {
                return std_synthesize3(this, spec, chain);
            }
            
            synth_result cegar_synthesize(synth_spec<TT,Solver>& spec, chain<TT,OpSize>& chain)
            {
                return cegar_std_synthesize(this, spec, chain);
            }
            
            synth_result cegar_synthesize3(synth_spec<TT,Solver>& spec, chain<TT,OpSize>& chain)
            {
                return cegar_std_synthesize3(this, spec, chain);
            }
    };

    /***************************************************************************
        Extends the alonce_synthesizer and adds clauses which ensure that no
        operand is ever re-applied (i.e. fully contained in another).
    ***************************************************************************/
    template<typename TT, typename Solver, int OpSize=2>
    class noreapply_synthesizer
    {
        public:
            void add_clauses(synth_spec<TT,Solver>& spec)
            {
                create_variables(spec);
                create_main_clauses(spec);
                create_output_clauses(spec);
                create_op_clauses(spec);
                create_nontriv_clauses(spec);
                create_alonce_clauses(spec);
                create_noreapply_clauses(spec);
            }
            
            void add_clauses3(synth_spec<TT,Solver>& spec)
            {
                create_variables3(spec);
                create_main_clauses3(spec);
                create_output_clauses(spec);
                create_op_clauses3(spec);
                create_nontriv_clauses3(spec);
                create_alonce_clauses3(spec);
                create_noreapply_clauses3(spec);
            }

            void cegar_add_clauses(synth_spec<TT,Solver>& spec)
            {
                create_variables(spec);
                create_output_clauses(spec);
                create_op_clauses(spec);
                create_nontriv_clauses(spec);
                create_alonce_clauses(spec);
                create_noreapply_clauses(spec);
            }

            void cegar_add_clauses3(synth_spec<TT,Solver>& spec)
            {
                create_variables3(spec);
                create_output_clauses(spec);
                create_op_clauses3(spec);
                create_nontriv_clauses3(spec);
                create_alonce_clauses3(spec);
                create_noreapply_clauses3(spec);
            }

            synth_result synthesize(synth_spec<TT,Solver>& spec, chain<TT,OpSize>& chain)
            {
                return std_synthesize(this, spec, chain);
            }
            
            synth_result synthesize3(synth_spec<TT,Solver>& spec, chain<TT,OpSize>& chain)
            {
                return std_synthesize3(this, spec, chain);
            }
            
            synth_result cegar_synthesize(synth_spec<TT,Solver>& spec, chain<TT,OpSize>& chain)
            {
                return cegar_std_synthesize(this, spec, chain);
            }
            
            synth_result cegar_synthesize3(synth_spec<TT,Solver>& spec, chain<TT,OpSize>& chain)
            {
                return cegar_std_synthesize3(this, spec, chain);
            }
    };

    /***************************************************************************
        Extends the noreapply_synthesizer and adds clauses which ensure that
        steps occur in co-lexicographic order.
    ***************************************************************************/
    template<typename TT, typename Solver, int OpSize=2>
    class colex_synthesizer
    {
        public:
            void add_clauses(synth_spec<TT,Solver>& spec)
            {
                create_variables(spec);
                create_main_clauses(spec);
                create_output_clauses(spec);
                create_op_clauses(spec);
                create_nontriv_clauses(spec);
                create_alonce_clauses(spec);
                create_noreapply_clauses(spec);
                create_colex_clauses(spec);
            }

            void add_clauses3(synth_spec<TT,Solver>& spec)
            {
                create_variables3(spec);
                create_main_clauses3(spec);
                create_output_clauses(spec);
                create_op_clauses3(spec);
                create_nontriv_clauses3(spec);
                create_alonce_clauses3(spec);
                create_noreapply_clauses3(spec);
                create_colex_clauses3(spec);
            }

            void cegar_add_clauses(synth_spec<TT,Solver>& spec)
            {
                create_variables(spec);
                create_output_clauses(spec);
                create_op_clauses(spec);
                create_nontriv_clauses(spec);
                create_alonce_clauses(spec);
                create_noreapply_clauses(spec);
                create_colex_clauses(spec);
            }

            void cegar_add_clauses3(synth_spec<TT,Solver>& spec)
            {
                create_variables3(spec);
                create_output_clauses(spec);
                create_op_clauses3(spec);
                create_nontriv_clauses3(spec);
                create_alonce_clauses3(spec);
                create_noreapply_clauses3(spec);
                create_colex_clauses3(spec);
            }

            synth_result synthesize(synth_spec<TT,Solver>& spec, chain<TT,OpSize>& chain)
            {
                return std_synthesize(this, spec, chain);
            }
            
            synth_result synthesize3(synth_spec<TT,Solver>& spec, chain<TT,OpSize>& chain)
            {
                return std_synthesize3(this, spec, chain);
            }
            
            synth_result cegar_synthesize(synth_spec<TT,Solver>& spec, chain<TT,OpSize>& chain)
            {
                return cegar_std_synthesize(this, spec, chain);
            }
            
            synth_result cegar_synthesize3(synth_spec<TT,Solver>& spec, chain<TT,OpSize>& chain)
            {
                return cegar_std_synthesize3(this, spec, chain);
            }
    };

    /***************************************************************************
        Extends the colex_synthesizer and adds clauses which ensure that
        step operators also occur in co-lexicographic order.
    ***************************************************************************/
    template<typename TT, typename Solver, int OpSize=2>
    class colex_func_synthesizer
    {
        public:
            void add_clauses(synth_spec<TT,Solver>& spec)
            {
                create_variables(spec);
                create_main_clauses(spec);
                create_output_clauses(spec);
                create_op_clauses(spec);
                create_nontriv_clauses(spec);
                create_alonce_clauses(spec);
                create_noreapply_clauses(spec);
                create_colex_clauses(spec);
                create_colex_func_clauses(spec);
            }

            void cegar_add_clauses(synth_spec<TT,Solver>& spec)
            {
                create_variables(spec);
                create_output_clauses(spec);
                create_op_clauses(spec);
                create_nontriv_clauses(spec);
                create_alonce_clauses(spec);
                create_noreapply_clauses(spec);
                create_colex_clauses(spec);
                create_colex_func_clauses(spec);
            }

            synth_result synthesize(synth_spec<TT,Solver>& spec, chain<TT,OpSize>& chain)
            {
                return std_synthesize(this, spec, chain);
            }

            synth_result cegar_synthesize(synth_spec<TT,Solver>& spec, chain<TT,OpSize>& chain)
            {
                return cegar_std_synthesize(this, spec, chain);
            }
    };

    /***************************************************************************
        Extends the colex_func_synthesizer and adds clauses which ensure that
        symmetric variables occur in order.
    ***************************************************************************/
    template<typename TT, typename Solver, int OpSize=2>
    class symmetric_synthesizer
    {
        public:
            void add_clauses(synth_spec<TT,Solver>& spec)
            {
                create_variables(spec);
                create_main_clauses(spec);
                create_output_clauses(spec);
                create_op_clauses(spec);
                create_nontriv_clauses(spec);
                create_alonce_clauses(spec);
                create_noreapply_clauses(spec);
                create_colex_clauses(spec);
                //create_colex_func_clauses(spec);
                create_symvar_clauses(spec);
            }

            void cegar_add_clauses(synth_spec<TT,Solver>& spec)
            {
                create_variables(spec);
                create_output_clauses(spec);
                create_op_clauses(spec);
                create_nontriv_clauses(spec);
                create_alonce_clauses(spec);
                create_noreapply_clauses(spec);
                create_colex_clauses(spec);
                //create_colex_func_clauses(spec);
                create_symvar_clauses(spec);
            }
            
            synth_result 
            find_chain(
                    synth_spec<TT,Solver>& spec, 
                    chain<TT,OpSize>& chain, 
                    int nr_steps)
            {
                assert(spec.nr_in <= 6);
                assert(spec.nr_out <= 64);

                spec_preprocess(spec);

                // The special case when the Boolean chain to be synthesized consists
                // entirely of trivial functions.
                if (spec.nr_triv == spec.nr_out) {
                    chain.reset(spec.nr_in, spec.nr_out, 0);
                    for (int h = 0; h < spec.nr_out; h++) {
                        chain.set_out(h, spec.triv_functions[h]);
                    }
                    return success;
                }
                
                spec.nr_steps = nr_steps;

                auto result = chain_exists(this, spec);
                if (result == success) {
                    chain_extract(spec, chain);
                }
                return result;
            }

            synth_result synthesize(synth_spec<TT,Solver>& spec, chain<TT,OpSize>& chain)
            {
                return std_synthesize(this, spec, chain);
            }

            synth_result cegar_synthesize(synth_spec<TT,Solver>& spec, chain<TT,OpSize>& chain)
            {
                return cegar_std_synthesize(this, spec, chain);
            }
    };

    /***************************************************************************
        Extends the colex_func_synthesizer and adds clauses that constrain the 
        synthesized Boolbean chain to specific graph topologies.
    ***************************************************************************/
    template<typename TT, typename Solver, int OpSize=2>
    class top_synthesizer
    {
        public:
            void add_clauses(synth_spec<TT,Solver>& spec)
            {
                top_create_variables(spec);
                top_create_main_clauses(spec);
                create_output_clauses(spec);
                top_create_op_clauses(spec);
                create_nontriv_clauses(spec);
                top_create_alonce_clauses(spec);
                top_create_noreapply_clauses(spec);
                top_create_colex_clauses(spec);
                //top_create_colex_func_clauses(spec);
                top_create_symvar_clauses(spec);
            }

            void add_clauses3(synth_spec<TT,Solver>& spec)
            {
                create_variables3(spec);
                create_main_clauses3(spec);
                create_output_clauses(spec);
                create_op_clauses3(spec);
                create_nontriv_clauses3(spec);
                create_alonce_clauses3(spec);
                create_noreapply_clauses3(spec);
                create_colex_clauses3(spec);
                create_topology_clauses3(spec);
            }

            void cegar_add_clauses(synth_spec<TT,Solver>& spec)
            {
                top_create_variables(spec);
                create_output_clauses(spec);
                top_create_op_clauses(spec);
                create_nontriv_clauses(spec);
                top_create_alonce_clauses(spec);
                top_create_noreapply_clauses(spec);
                top_create_colex_clauses(spec);
                //top_create_colex_func_clauses(spec);
                top_create_symvar_clauses(spec);
            }

            void cegar_add_clauses3(synth_spec<TT,Solver>& spec)
            {
                create_variables3(spec);
                create_output_clauses(spec);
                create_op_clauses3(spec);
                create_nontriv_clauses3(spec);
                create_alonce_clauses3(spec);
                create_noreapply_clauses3(spec);
                create_colex_clauses3(spec);
                create_topology_clauses3(spec);
            }

            synth_result synthesize(synth_spec<TT,Solver>& spec, chain<TT,OpSize>& chain)
            {
                return top_synthesize(this, spec, chain);
            }

            synth_result synthesize3(synth_spec<TT,Solver>& spec, chain<TT,OpSize>& chain)
            {
                return top_synthesize3(this, spec, chain);
            }
            
            synth_result cegar_synthesize(synth_spec<TT,Solver>& spec, chain<TT,OpSize>& chain)
            {
                return cegar_top_synthesize(this, spec, chain);
            }

            synth_result cegar_synthesize3(synth_spec<TT,Solver>& spec, chain<TT,OpSize>& chain)
            {
                return cegar_top_synthesize3(this, spec, chain);
            }
    };

    template<typename TT, typename Solver, typename Generator>
    void 
    top_synthesize_parallel(
            const synth_spec<TT,Solver>& main_spec, chain<TT>& chain, 
            synth_result& result, bool& stop, Generator& gen, 
            std::mutex& gen_mutex)
    {
        // We cannot directly copy the spec. We need each thread to have its
        // own specification and solver to avoid threading issues.
        synth_spec<TT,Solver> spec;
        spec.nr_in = main_spec.nr_in;
        spec.nr_out = main_spec.nr_out;
        spec.verbosity = main_spec.verbosity;
        spec.conflict_limit = main_spec.conflict_limit;
        
        if (spec.verbosity > 2) {
            printf("Thread %lu START\n", std::this_thread::get_id());
        }

        for (int i = 0; i < MAX_OUT; i++) {
            spec.functions[i] = main_spec.functions[i];
        }

        top_synthesizer<TT,Solver> synth;

        spec_preprocess(spec);
        
        // The special case when the Boolean chain to be synthesized consists
        // entirely of trivial functions.
        if (spec.nr_triv == spec.nr_out) {
            chain.reset(spec.nr_in, spec.nr_out, 0);
            for (int h = 0; h < spec.nr_out; h++) {
                chain.set_out(h, spec.triv_functions[h]);
            }
            std::lock_guard<std::mutex> gen_lock(gen_mutex);
            if (spec.verbosity > 2) {
                printf("Thread %lu SOLUTION(0)\n", std::this_thread::get_id());
            }
            stop = true;
            result = success;
            return;
        }

        // As the topological synthesizer decomposes the synthesis problem,
        // to fairly count the total number of conflicts we should keep track
        // of all conflicts in existence checks.
        int total_conflicts = 0;
        fence f;
        int old_nnodes = 1;
        while (true) {
            {
                std::lock_guard<std::mutex> gen_lock(gen_mutex);
                if (stop) {
                    if (spec.verbosity > 2) {
                        printf("Thread %lu RETURN\n", 
                                std::this_thread::get_id());
                    }
                    return;
                }
                gen.next_fence(f);
            }
            spec.nr_steps = f.nr_nodes();
            spec.update_level_map(f);
            
            if (spec.nr_steps > old_nnodes) {
                // Reset conflict count, since this is where other synthesizers
                // reset it.
                total_conflicts = 0;
                old_nnodes = spec.nr_steps;
            }

            if (spec.verbosity > 2) {
                printf("  next fence:\n");
                print_fence(f);
                printf("\n");
                printf("nr_nodes=%d, nr_levels=%d\n", f.nr_nodes(), 
                        f.nr_levels());
                for (int i = 0; i < f.nr_levels(); i++) {
                    printf("f[%d] = %d\n", i, f[i]);
                }
            }
            // Add the clauses that encode the main constraints, but not
            // yet any DAG structure.
            auto status = chain_exists(&synth, spec);
            if (status == success) {
                top_chain_extract(spec, chain);
                std::lock_guard<std::mutex> gen_lock(gen_mutex);
                stop = true;
                if (spec.verbosity > 2) {
                    printf("Thread %lu SOLUTION(%d)\n", 
                            std::this_thread::get_id(), chain.nr_steps());
                }
                result = success;
                return;
            } else if (status == failure) {
                {
                    std::lock_guard<std::mutex> gen_lock(gen_mutex);
                    if (stop) {
                        if (spec.verbosity > 2) {
                            printf("Thread %lu RETURN\n", 
                                    std::this_thread::get_id());
                        }
                        return;
                    }
                }
                total_conflicts += solver_nr_conflicts(spec.solver());
                if (spec.conflict_limit &&
                        total_conflicts > spec.conflict_limit) {
                    if (spec.verbosity > 2) {
                        printf("Thread %lu TIMEOUT\n",
                                std::this_thread::get_id());
                    }
                    return;
                }
                continue;
            } else {
                if (spec.verbosity > 2) {
                    printf("Thread %lu TIMEOUT\n", std::this_thread::get_id());
                }
                return;
            }
        }
    }


    template<typename TT, typename Solver, typename Generator>
    void 
    top_synthesize_parallel3(
            const synth_spec<TT,Solver>& main_spec, chain<TT,3>& chain, 
            synth_result& result, bool& stop, Generator& gen, 
            std::mutex& gen_mutex)
    {
        // We cannot directly copy the spec. We need each thread to have its own
        // specification and solver to avoid threading issues.
        synth_spec<TT,Solver> spec;
        spec.nr_in = main_spec.nr_in;
        spec.nr_out = main_spec.nr_out;
        spec.verbosity = main_spec.verbosity;
        spec.conflict_limit = main_spec.conflict_limit;
        
        if (spec.verbosity > 2) {
            printf("Thread %lu START\n", std::this_thread::get_id());
        }

        for (int i = 0; i < MAX_OUT; i++) {
            spec.functions[i] = main_spec.functions[i];
        }

        top_synthesizer<TT,Solver,3> synth;

        spec_preprocess(spec);
        
        // The special case when the Boolean chain to be synthesized consists
        // entirely of trivial functions.
        if (spec.nr_triv == spec.nr_out) {
            chain.reset(spec.nr_in, spec.nr_out, 0);
            for (int h = 0; h < spec.nr_out; h++) {
                chain.set_out(h, spec.triv_functions[h]);
            }
            std::lock_guard<std::mutex> gen_lock(gen_mutex);
            if (spec.verbosity > 2) {
                printf("Thread %lu SOLUTION(0)\n", std::this_thread::get_id());
            }
            stop = true;
            result = success;
            return;
        }

        // As the topological synthesizer decomposes the synthesis problem,
        // to fairly count the total number of conflicts we should keep track
        // of all conflicts in existence checks.
        int total_conflicts = 0;
        fence f;
        int old_nnodes = 1;
        while (true) {
            {
                std::lock_guard<std::mutex> gen_lock(gen_mutex);
                if (stop) {
                    if (spec.verbosity > 2) {
                        printf("Thread %lu RETURN\n", 
                                std::this_thread::get_id());
                    }
                    return;
                }
                gen.next_fence(f);
            }
            spec.nr_steps = f.nr_nodes();
            spec.update_level_map(f);
            
            if (spec.nr_steps > old_nnodes) {
                // Reset conflict count, since this is where other synthesizers
                // reset it.
                total_conflicts = 0;
                old_nnodes = spec.nr_steps;
            }

            if (spec.verbosity > 2) {
                printf("  next fence:\n");
                print_fence(f);
                printf("\n");
                printf("nr_nodes=%d, nr_levels=%d\n", f.nr_nodes(), 
                        f.nr_levels());
                for (int i = 0; i < f.nr_levels(); i++) {
                    printf("f[%d] = %d\n", i, f[i]);
                }
            }
            // Add the clauses that encode the main constraints, but not
            // yet any DAG structure.
            auto status = chain_exists3(&synth, spec);
            if (status == success) {
                chain_extract3(spec, chain);
                std::lock_guard<std::mutex> gen_lock(gen_mutex);
                stop = true;
                if (spec.verbosity > 2) {
                    printf("Thread %lu SOLUTION(%d)\n", 
                            std::this_thread::get_id(), chain.nr_steps());
                }
                result = success;
                return;
            } else if (status == failure) {
                {
                    std::lock_guard<std::mutex> gen_lock(gen_mutex);
                    if (stop) {
                        if (spec.verbosity > 2) {
                            printf("Thread %lu RETURN\n", 
                                    std::this_thread::get_id());
                        }
                        return;
                    }
                }
                total_conflicts += solver_nr_conflicts(spec.solver());
                if (spec.conflict_limit &&
                        total_conflicts > spec.conflict_limit) {
                    if (spec.verbosity > 2) {
                        printf("Thread %lu TIMEOUT\n",
                                std::this_thread::get_id());
                    }
                    return;
                }
                continue;
            } else {
                if (spec.verbosity > 2) {
                    printf("Thread %lu TIMEOUT\n", std::this_thread::get_id());
                }
                return;
            }
        }
    }

    template<typename TT, typename Solver, typename Generator>
    void 
    cegar_top_synthesize_parallel(
            const synth_spec<TT,Solver>& main_spec, chain<TT>& chain, 
            synth_result& result, bool& stop, Generator& gen, 
            std::mutex& gen_mutex)
    {
        // We cannot directly copy the spec. We need each thread to have its own
        // specification and solver to avoid threading issues.
        synth_spec<TT,Solver> spec;
        spec.nr_in = main_spec.nr_in;
        spec.nr_out = main_spec.nr_out;
        spec.verbosity = main_spec.verbosity;
        spec.conflict_limit = main_spec.conflict_limit;
        
        if (spec.verbosity > 2) {
            printf("Thread %lu START\n", std::this_thread::get_id());
        }

        for (int i = 0; i < MAX_OUT; i++) {
            spec.functions[i] = main_spec.functions[i];
        }

        top_synthesizer<TT,Solver> synth;
        spec_preprocess(spec);
        spec.nr_rand_tt_assigns = 2*spec.nr_in;
        
        // The special case when the Boolean chain to be synthesized consists
        // entirely of trivial functions.
        if (spec.nr_triv == spec.nr_out) {
            chain.reset(spec.nr_in, spec.nr_out, 0);
            for (int h = 0; h < spec.nr_out; h++) {
                chain.set_out(h, spec.triv_functions[h]);
            }
            std::lock_guard<std::mutex> gen_lock(gen_mutex);
            if (spec.verbosity > 2) {
                printf("Thread %lu SOLUTION(0)\n", std::this_thread::get_id());
            }
            stop = true;
            result = success;
            return;
        }

        // As the topological synthesizer decomposes the synthesis problem,
        // to fairly count the total number of conflicts we should keep track
        // of all conflicts in existence checks.
        int total_conflicts = 0;
        fence f;
        int old_nnodes = 1;
        while (true) {
            {
                std::lock_guard<std::mutex> gen_lock(gen_mutex);
                if (stop) {
                    if (spec.verbosity > 2) {
                        printf("Thread %lu RETURN\n", 
                                std::this_thread::get_id());
                    }
                    return;
                }
                gen.next_fence(f);
            }
            spec.nr_steps = f.nr_nodes();
            spec.update_level_map(f);
            
            if (spec.nr_steps > old_nnodes) {
                // Reset conflict count, since this is where other synthesizers
                // reset it.
                total_conflicts = 0;
                old_nnodes = spec.nr_steps;
            }

            if (spec.verbosity) {
                printf("  next fence:\n");
                print_fence(f);
                printf("\n");
                printf("nr_nodes=%d, nr_levels=%d\n", f.nr_nodes(), 
                        f.nr_levels());
                for (int i = 0; i < f.nr_levels(); i++) {
                    printf("f[%d] = %d\n", i, f[i]);
                }
            }
            // Add the clauses that encode the main constraints, but not
            // yet any DAG structure.
            auto status = cegar_top_chain_exists(&synth, spec, chain);
            if (status == success) {
                top_chain_extract(spec, chain);
                std::lock_guard<std::mutex> gen_lock(gen_mutex);
                stop = true;
                if (spec.verbosity > 2) {
                    printf("Thread %lu SOLUTION(%d)\n", 
                            std::this_thread::get_id(), chain.nr_steps());
                }
                result = success;
                return;
            } else if (status == failure) {
                {
                    std::lock_guard<std::mutex> gen_lock(gen_mutex);
                    if (stop) {
                        if (spec.verbosity > 2) {
                            printf("Thread %lu RETURN\n", 
                                    std::this_thread::get_id());
                        }
                        return;
                    }
                }
                total_conflicts += solver_nr_conflicts(spec.solver());
                if (spec.conflict_limit &&
                        total_conflicts > spec.conflict_limit) {
                    if (spec.verbosity > 2) {
                        printf("Thread %lu TIMEOUT\n",
                                std::this_thread::get_id());
                    }
                    return;
                }
                continue;
            } else {
                if (spec.verbosity > 2) {
                    printf("Thread %lu TIMEOUT\n", std::this_thread::get_id());
                }
                return;
            }
        }
    }

    template<typename TT, typename Solver, typename Generator>
    void 
    cegar_top_synthesize_parallel3(
            const synth_spec<TT,Solver>& main_spec, chain<TT,3>& chain, 
            synth_result& result, bool& stop, Generator& gen, 
            std::mutex& gen_mutex)
    {
        // We cannot directly copy the spec. We need each thread to have its own
        // specification and solver to avoid threading issues.
        synth_spec<TT,Solver> spec;
        spec.nr_in = main_spec.nr_in;
        spec.nr_out = main_spec.nr_out;
        spec.verbosity = main_spec.verbosity;
        spec.conflict_limit = main_spec.conflict_limit;
        
        if (spec.verbosity > 2) {
            printf("Thread %lu START\n", std::this_thread::get_id());
        }

        for (int i = 0; i < MAX_OUT; i++) {
            spec.functions[i] = main_spec.functions[i];
        }

        top_synthesizer<TT,Solver,3> synth;
        spec_preprocess(spec);
        spec.nr_rand_tt_assigns = 2*spec.nr_in;
        
        // The special case when the Boolean chain to be synthesized consists
        // entirely of trivial functions.
        if (spec.nr_triv == spec.nr_out) {
            chain.reset(spec.nr_in, spec.nr_out, 0);
            for (int h = 0; h < spec.nr_out; h++) {
                chain.set_out(h, spec.triv_functions[h]);
            }
            std::lock_guard<std::mutex> gen_lock(gen_mutex);
            if (spec.verbosity > 2) {
                printf("Thread %lu SOLUTION(0)\n", std::this_thread::get_id());
            }
            stop = true;
            result = success;
            return;
        }

        // As the topological synthesizer decomposes the synthesis problem,
        // to fairly count the total number of conflicts we should keep track
        // of all conflicts in existence checks.
        int total_conflicts = 0;
        fence f;
        int old_nnodes = 1;
        while (true) {
            {
                std::lock_guard<std::mutex> gen_lock(gen_mutex);
                if (stop) {
                    if (spec.verbosity > 2) {
                        printf("Thread %lu RETURN\n", 
                                std::this_thread::get_id());
                    }
                    return;
                }
                gen.next_fence(f);
            }
            spec.nr_steps = f.nr_nodes();
            spec.update_level_map(f);
            
            if (spec.nr_steps > old_nnodes) {
                // Reset conflict count, since this is where other synthesizers
                // reset it.
                total_conflicts = 0;
                old_nnodes = spec.nr_steps;
            }

            if (spec.verbosity) {
                printf("  next fence:\n");
                print_fence(f);
                printf("\n");
                printf("nr_nodes=%d, nr_levels=%d\n", f.nr_nodes(), 
                        f.nr_levels());
                for (int i = 0; i < f.nr_levels(); i++) {
                    printf("f[%d] = %d\n", i, f[i]);
                }
            }
            // Add the clauses that encode the main constraints, but not
            // yet any DAG structure.
            auto status = cegar_chain_exists3(&synth, spec, chain);
            if (status == success) {
                chain_extract3(spec, chain);
                std::lock_guard<std::mutex> gen_lock(gen_mutex);
                stop = true;
                if (spec.verbosity > 2) {
                    printf("Thread %lu SOLUTION(%d)\n", 
                            std::this_thread::get_id(), chain.nr_steps());
                }
                result = success;
                return;
            } else if (status == failure) {
                {
                    std::lock_guard<std::mutex> gen_lock(gen_mutex);
                    if (stop) {
                        if (spec.verbosity > 2) {
                            printf("Thread %lu RETURN\n", 
                                    std::this_thread::get_id());
                        }
                        return;
                    }
                }
                total_conflicts += solver_nr_conflicts(spec.solver());
                if (spec.conflict_limit &&
                        total_conflicts > spec.conflict_limit) {
                    if (spec.verbosity > 2) {
                        printf("Thread %lu TIMEOUT\n",
                                std::this_thread::get_id());
                    }
                    return;
                }
                continue;
            } else {
                if (spec.verbosity > 2) {
                    printf("Thread %lu TIMEOUT\n", std::this_thread::get_id());
                }
                return;
            }
        }
    }

    template<typename TT, typename Solver>
    synth_result 
    synthesize_parallel(
            const synth_spec<TT,Solver>& spec, const int nr_threads, 
            chain<TT>& chain)
    {
        po_filter<unbounded_generator> g(unbounded_generator(), 1, 2);
        std::mutex m;
        std::vector<std::thread> threads(nr_threads);
        std::vector<percy::chain<TT>> chains(nr_threads);
        std::vector<synth_result> statuses(nr_threads);
        bool stop = false;

        for (int i = 0; i < nr_threads; i++) {
            statuses[i] = timeout;
        }

        for (int i = 0; i < nr_threads; i++) {
            auto& c = chains[i];
            auto& status = statuses[i];
            threads[i] = std::thread([&spec, &c, &status, &stop, &g, &m] {
                    top_synthesize_parallel(spec, c, status, stop, g, m);
            });
        }

        if (spec.verbosity) {
            printf("\n\nSTARTED THREADS\n\n");
        }

        for (auto& t : threads) {
            t.join();
        }

        int best_sol = 1000000; // Arbitrary large number
        bool had_success = false;
        for (int i = 0; i < nr_threads; i++) {
            if (statuses[i] == success) {
                if (chains[i].nr_steps() < best_sol) {
                    best_sol = chains[i].nr_steps();
                    chain.copy(chains[i]);
                    had_success = true;
                }
            }
        }

        if (had_success) {
            return success;
        } else {
            return timeout;
        }
    }


    template<typename TT, typename Solver>
    synth_result 
    synthesize_parallel3(
            const synth_spec<TT,Solver>& spec, const int nr_threads, 
            chain<TT,3>& chain)
    {
        po_filter<unbounded_generator> g(unbounded_generator(), 1, 2);
        std::mutex m;
        std::vector<std::thread> threads(nr_threads);
        std::vector<percy::chain<TT,3>> chains(nr_threads);
        std::vector<synth_result> statuses(nr_threads);
        bool stop = false;

        for (int i = 0; i < nr_threads; i++) {
            statuses[i] = timeout;
        }

        for (int i = 0; i < nr_threads; i++) {
            auto& c = chains[i];
            auto& status = statuses[i];
            threads[i] = std::thread([&spec, &c, &status, &stop, &g, &m] {
                    top_synthesize_parallel3(spec, c, status, stop, g, m);
            });
        }

        if (spec.verbosity) {
            printf("\n\nSTARTED THREADS\n\n");
        }

        for (auto& t : threads) {
            t.join();
        }

        int best_sol = 1000000; // Arbitrary large number
        bool had_success = false;
        for (int i = 0; i < nr_threads; i++) {
            if (statuses[i] == success) {
                if (chains[i].nr_steps() < best_sol) {
                    best_sol = chains[i].nr_steps();
                    chain.copy(chains[i]);
                    had_success = true;
                }
            }
        }

        if (had_success) {
            return success;
        } else {
            return timeout;
        }
    }

    template<typename TT, typename Solver>
    synth_result 
    cegar_synthesize_parallel(
            const synth_spec<TT,Solver>& spec, const int nr_threads, 
            chain<TT>& chain)
    {
        po_filter<unbounded_generator> g(unbounded_generator(), 1, 2);
        std::mutex m;
        std::vector<std::thread> threads(nr_threads);
        std::vector<percy::chain<TT>> chains(nr_threads);
        std::vector<synth_result> statuses(nr_threads);
        bool stop = false;

        for (int i = 0; i < nr_threads; i++) {
            statuses[i] = timeout;
        }

        for (int i = 0; i < nr_threads; i++) {
            auto& c = chains[i];
            auto& status = statuses[i];
            threads[i] = std::thread([&spec, &c, &status, &stop, &g, &m] {
                    cegar_top_synthesize_parallel(spec, c, status, stop, g, m);
            });
        }

        if (spec.verbosity) {
            printf("\n\nSTARTED THREADS\n\n");
        }

        for (auto& t : threads) {
            t.join();
        }

        int best_sol = 1000000; // Arbitrary large number
        bool had_success = false;
        for (int i = 0; i < nr_threads; i++) {
            if (statuses[i] == success) {
                if (chains[i].nr_steps() < best_sol) {
                    best_sol = chains[i].nr_steps();
                    chain.copy(chains[i]);
                    had_success = true;
                }
            }
        }

        if (had_success) {
            return success;
        } else {
            return timeout;
        }
    }

    template<typename TT, typename Solver>
    synth_result 
    cegar_synthesize_parallel3(
            const synth_spec<TT,Solver>& spec, const int nr_threads, 
            chain<TT,3>& chain)
    {
        po_filter<unbounded_generator> g(unbounded_generator(), 1, 2);
        std::mutex m;
        std::vector<std::thread> threads(nr_threads);
        std::vector<percy::chain<TT,3>> chains(nr_threads);
        std::vector<synth_result> statuses(nr_threads);
        bool stop = false;

        for (int i = 0; i < nr_threads; i++) {
            statuses[i] = timeout;
        }

        for (int i = 0; i < nr_threads; i++) {
            auto& c = chains[i];
            auto& status = statuses[i];
            threads[i] = std::thread([&spec, &c, &status, &stop, &g, &m] {
                    cegar_top_synthesize_parallel3(spec, c, status, stop, g, m);
            });
        }

        if (spec.verbosity) {
            printf("\n\nSTARTED THREADS\n\n");
        }

        for (auto& t : threads) {
            t.join();
        }

        int best_sol = 1000000; // Arbitrary large number
        bool had_success = false;
        for (int i = 0; i < nr_threads; i++) {
            if (statuses[i] == success) {
                if (chains[i].nr_steps() < best_sol) {
                    best_sol = chains[i].nr_steps();
                    chain.copy(chains[i]);
                    had_success = true;
                }
            }
        }

        if (had_success) {
            return success;
        } else {
            return timeout;
        }
    }

    /***************************************************************************
        Finds the smallest possible DAG that can implement the specified
        function.
    ***************************************************************************/
    template<typename TT>
    synth_result find_dag(const TT& f, dag& g, int nr_vars)
    {
        chain<TT> chain;
        rec_dag_generator gen;
        dag_synthesizer<TT, sat_solver*> synth;

        int nr_vertices = 1;
        while (true) {
            gen.reset(nr_vars, nr_vertices);
            g.reset(nr_vars, nr_vertices);
            synth.reset(nr_vars, nr_vertices);
            const auto result = gen.find_dag(f, g, chain, synth);
            if (result == success) {
                return success;
            }
            nr_vertices++;
        }
        return failure;
    }

    /***************************************************************************
        Finds a DAG of the specified size that can implement the given
        function (if one exists).
    ***************************************************************************/
    template<typename TT>
    synth_result 
    find_dag(const TT& f, dag& g, int nr_vars, int nr_vertices)
    {
        chain<TT> chain;
        rec_dag_generator gen;
        dag_synthesizer<TT, sat_solver*> synth;

        gen.reset(nr_vars, nr_vertices);
        g.reset(nr_vars, nr_vertices);
        synth.reset(nr_vars, nr_vertices);
        return gen.find_dag(f, g, chain, synth);
    }


    /***************************************************************************
        A parallel version of the find_dag function.
    ***************************************************************************/
    template<typename TT>
    synth_result 
    pfind_dag(
            const TT& function, 
            dag& g, 
            int nr_vars, 
            int nr_threads)
    {
        int nr_vertices = 1;
        while (true) {
            const auto status = pfind_dag<TT>(
                    function, g, nr_vars, nr_vertices, nr_threads);
            if (status == success) {
                return success;
            }
            nr_vertices++;
        }
        
        return failure;
    }

    template<typename TT>
    synth_result 
    pfind_dag(
            const TT& f, 
            dag& g, 
            int nr_vars, 
            int nr_vertices, 
            int nr_threads)
    {
        vector<std::thread> threads;
        
        int nr_branches = 0;
        vector<pair<int,int>> starting_points;
        for (int k = 1; k < nr_vars; k++) {
            for (int j = 0; j < k; j++) {
                ++nr_branches;
                starting_points.push_back(std::make_pair(j, k));
            }
        }
        if (nr_branches > nr_threads) {
            printf("Error: unable to distribute %d branches over %d "
                    "threads\n", nr_branches, nr_threads);
            return failure;
        }
        
        auto solv = new synth_result[starting_points.size()];
        vector<dag> dags(starting_points.size());
        std::mutex vmutex;
        std::mutex found_mutex;
        bool found = false;
        bool* found_ptr = &found;

        for (int i = 0; i < starting_points.size(); i++) {
            const auto& sp = starting_points[i];
            threads.push_back(
                std::thread(
                    [i, &f, &dags, &vmutex, solv, &sp, nr_vars,
                    nr_vertices, &found_mutex, found_ptr] {
                    dag local_g;
                    chain<TT> chain;
                    rec_dag_generator gen;
                    dag_synthesizer<TT, sat_solver*> synth;

                    gen.reset(nr_vars, nr_vertices);
                    local_g.reset(nr_vars, nr_vertices);
                    synth.reset(nr_vars, nr_vertices);
                    gen.add_selection(sp.first, sp.second);
                    const auto status = gen.pfind_dag(f, local_g, chain, 
                            synth, found_ptr, found_mutex);
                    {
                        std::lock_guard<std::mutex> vlock(vmutex);
                        solv[i] = status;
                        if (status == success) {
                            dags[i] = local_g;
                        }
                    }
                }
            ));
        }

        for (auto& t : threads) {
            t.join();
        }

        auto status = failure;
        int nr_found = 0;
        for (int i = 0; i < starting_points.size(); i++) {
            if (solv[i] == success) {
                const auto& local_g = dags[i];
                g.reset(nr_vars, nr_vertices);
                for (int i = 0; i < nr_vertices; i++ ){
                    const auto& vertex = local_g.get_vertex(i);
                    g.set_vertex(i, vertex.first, vertex.second);
                }
                status = success;
                ++nr_found;
            }
        }
        assert(nr_found <= 1);

        delete[] solv;

        return status;
    }

    template<typename TT>
    synth_result 
    qpfind_dag(
            const TT& function, 
            dag& g, 
            int nr_vars,
            bool verbose=false)
    {
        int nr_vertices = 1;
        while (true) {
            if (verbose) {
                fprintf(stderr, "Trying with %d vertices\n", nr_vertices);
                fflush(stderr);
            }
            const auto status = qpfind_dag<TT>(
                    function, g, nr_vars, nr_vertices);
            if (status == success) {
                return success;
            }
            nr_vertices++;
        }
        
        return failure;
    }

    template<typename TT>
    synth_result 
    qpfind_dag(
            const TT& f, 
            dag& g, 
            int nr_vars, 
            int nr_vertices)
    {
        vector<std::thread> threads;
       
        const auto nr_threads = std::thread::hardware_concurrency() - 1;
        
        moodycamel::ConcurrentQueue<dag> q(nr_threads*3);
        

        bool finished_generating = false;
        bool* pfinished = &finished_generating;
        bool found = false;
        bool* pfound = &found;
        std::mutex found_mutex;

        g.reset(nr_vars, nr_vertices);
        for (int i = 0; i < nr_threads; i++) {
            threads.push_back(
                std::thread([&f, pfinished, pfound, &found_mutex, &g, 
                            &q, nr_vars, nr_vertices] {
                    dag local_dag;
                    chain<TT> chain;
                    dag_synthesizer<TT, sat_solver*> synth;
                    synth.reset(nr_vars, nr_vertices);

                    while (!(*pfound)) {
                        if (!q.try_dequeue(local_dag)) {
                            if (*pfinished) {
                                if (!q.try_dequeue(local_dag)) {
                                    break;
                                }
                            } else {
                                std::this_thread::yield();
                                continue;
                            }
                        }
                        const auto status = 
                            synth.synthesize(f, local_dag, chain);

                        if (status == success) {
                            std::lock_guard<std::mutex> vlock(found_mutex);
                            if (!(*pfound)) {
                                for (int j = 0; j < nr_vertices; j++) {
                                    const auto& v = local_dag.get_vertex(j);
                                    g.set_vertex(j, v.first, v.second);
                                }
                                *pfound = true;
                            }
                        }
                    }
                }
            ));
        }

        rec_dag_generator gen;
        gen.reset(nr_vars, nr_vertices);
        gen.qpfind_dag(q, pfound);
        finished_generating = true;

        // After the generating thread has finished, we have room to spare
        // for another thread (if no solution was found yet.)
        if (!found) {
            dag local_dag;
            chain<TT> chain;
            dag_synthesizer<TT, sat_solver*> synth;
            synth.reset(nr_vars, nr_vertices);

            while (!found) {
                if (!q.try_dequeue(local_dag)) {
                    break;
                }
                const auto status = synth.synthesize(f, local_dag, chain);

                if (status == success) {
                    std::lock_guard<std::mutex> vlock(found_mutex);
                    if (!(found)) {
                        for (int j = 0; j < nr_vertices; j++) {
                            const auto& v = local_dag.get_vertex(j);
                            g.set_vertex(j, v.first, v.second);
                        }
                        found = true;
                    }
                }
            }
        }

        for (auto& t : threads) {
            t.join();
        }

        return found ? success : failure;
    }

    template<typename TT>
    synth_result 
    qpfence_synth(
            synth_stats* stats,
            const TT& function, 
            dag& g, 
            int nr_vars,
            int conflict_limit)
    {
        int nr_vertices = 1;
        while (true) {
            const auto status = qpfence_synth<TT>(
                    stats, function, g, nr_vars, nr_vertices, conflict_limit);
            if (status == success) {
                return success;
            }
            nr_vertices++;
        }
        
        return failure;
    }

    template<typename TT>
    synth_result 
    qpfence_synth(
            synth_stats* stats,
            const TT& f, 
            dag& g, 
            int nr_vars, 
            int nr_vertices,
            int conflict_limit)
    {
        vector<std::thread> threads;
        moodycamel::ConcurrentQueue<fence> q(1u << (nr_vertices - 1));
        
        const auto nr_threads = std::thread::hardware_concurrency() - 1;

        bool finished_generating = false;
        bool* pfinished = &finished_generating;
        bool found = false;
        bool* pfound = &found;
        std::mutex found_mutex;
        
        auto start = high_resolution_clock::now();
        time_point<high_resolution_clock> first_synth_time;

        stats->overhead = 0;
        stats->time_to_first_synth = 0;
        stats->total_synth_time = 0;

        for (int i = 0; i < nr_threads; i++) {
            threads.push_back(
                std::thread([&f, pfinished, pfound, &found_mutex, &g, &q, 
                    nr_vars, nr_vertices, &first_synth_time, conflict_limit] {
                    chain<TT> chain;
                    fence local_fence;
                    synth_spec<TT, sat_solver*> local_spec;
                    top_synthesizer<TT, sat_solver*> synth;

                    local_spec.nr_in = nr_vars;
                    local_spec.nr_out = 1;
                    local_spec.verbosity = 0;
                    local_spec.nr_steps = nr_vertices;
                    local_spec.functions[0] = &f;
                    local_spec.nr_rand_tt_assigns = 2 * local_spec.nr_in;
                    local_spec.conflict_limit = conflict_limit;

                    spec_preprocess(local_spec);

                    while (!(*pfound)) {
                        if (!q.try_dequeue(local_fence)) {
                            if (*pfinished) {
                                if (!q.try_dequeue(local_fence)) {
                                    break;
                                }
                            } else {
                                std::this_thread::yield();
                                continue;
                            }
                        }

                        local_spec.update_level_map(local_fence);
                        auto status = pcegar_top_chain_exists(&synth, 
                                local_spec, chain, pfound);

                        if (status == success) {
                            std::lock_guard<std::mutex> vlock(found_mutex);
                            if (!(*pfound)) {
                                first_synth_time = high_resolution_clock::now();
                                chain.extract_dag(g);
                                *pfound = true;
                            }
                        }
                    }
                }
            ));
        }

        generate_fences(nr_vertices, q);
        finished_generating = true;

        // After the generating thread has finished, we have room to spare
        // for another thread (if no solution was found yet.)
        {
            chain<TT> chain;
            fence local_fence;
            synth_spec<TT, sat_solver*> local_spec;
            top_synthesizer<TT, sat_solver*> synth;

            local_spec.nr_in = nr_vars;
            local_spec.nr_out = 1;
            local_spec.verbosity = 0;
            local_spec.nr_steps = nr_vertices;
            local_spec.functions[0] = &f;
            local_spec.nr_rand_tt_assigns = 2 * local_spec.nr_in;
            local_spec.conflict_limit = conflict_limit;

            spec_preprocess(local_spec);

            while (!(found)) {
                if (!q.try_dequeue(local_fence)) {
                    if (finished_generating) {
                        if (!q.try_dequeue(local_fence)) {
                            break;
                        }
                    } else {
                        std::this_thread::yield();
                        continue;
                    }
                }

                local_spec.update_level_map(local_fence);
                auto status = pcegar_top_chain_exists(&synth, local_spec,
                        chain, pfound);

                if (status == success) {
                    std::lock_guard<std::mutex> vlock(found_mutex);
                    if (!(found)) {
                        first_synth_time = high_resolution_clock::now();
                        chain.extract_dag(g);
                        found = true;
                    }
                }
            }
        }

        for (auto& t : threads) {
            t.join();
        }
        if (found) {
            const auto total_synth_time = duration<double,std::milli>(
                    high_resolution_clock::now() - start).count();
    
            const auto time_to_first_synth = duration<double,std::milli>(
                    first_synth_time - start).count();

            const auto overhead = total_synth_time - time_to_first_synth;

            stats->overhead = overhead;
            stats->time_to_first_synth = time_to_first_synth;
            stats->total_synth_time = total_synth_time;


            /*
            printf("Time to first synth: %.2fms\n", 
                    std::chrono::duration<double,std::milli>(
                        time_to_synth-start).count());
            printf("Total synth time: %.2fms\n", 
                    std::chrono::duration<double,std::milli>(
                        total_synth_time-start).count());
                        */
        }


        return found ? success : failure;
    }

    uint64_t 
    parallel_dag_count(int nr_vars, int nr_vertices, int nr_threads)
    {
        printf("Initializing %d-thread parallel DAG count\n", nr_threads);
        vector<std::thread> threads;

        int nr_branches = 0;
        vector<pair<int,int>> starting_points;
        for (int k = 1; k < nr_vars; k++) {
            for (int j = 0; j < k; j++) {
                ++nr_branches;
                starting_points.push_back(std::make_pair(j, k));
            }
        }
        printf("Nr. root branches: %d\n", nr_branches);
        if (nr_branches > nr_threads) {
            printf("Error: unable to distribute %d branches over %d "
                    "threads\n", nr_branches, nr_threads);
            return 0;
        }

        // Each thread will write the number of solutions it has found to this
        // array.
        auto solv = new uint64_t[starting_points.size()];
        
        for (int i = 0; i < starting_points.size(); i++) {
            const auto& sp = starting_points[i];
            threads.push_back(
                std::thread([i, solv, &sp, nr_vars, nr_vertices] {
                    printf("Starting thread %d\n", i+1);

                    rec_dag_generator gen;
                    gen.reset(nr_vars, nr_vertices);
                    gen.add_selection(sp.first, sp.second);
                    const auto nsols = gen.count_dags();
                    solv[i] = nsols;
                }
            ));
        }

        for (auto& t : threads) {
            t.join();
        }

        uint64_t total_nsols =0 ;
        for (int i = 0; i < starting_points.size(); i++) {
            printf("solv[%d] = %lu\n", i, solv[i]);
            total_nsols += solv[i];
        }
        printf("total_nsols=%lu\n", total_nsols);

        delete[] solv;

        return total_nsols;
    }

    vector<dag> 
    parallel_dag_gen(int nr_vars, int nr_vertices, int nr_threads)
    {
        printf("Initializing %d-thread parallel DAG gen\n", nr_threads);
        printf("nr_vars=%d, nr_vertices=%d\n", nr_vars, nr_vertices);
        vector<std::thread> threads;

        // Each thread will write the DAGs it has found to this vector.
        vector<dag> dags;

        // First estimate the number of solutions down each branch by looking
        // at DAGs with small numbers of vertices.
        int nr_branches = 0;
        vector<pair<int,int>> starting_points;
        for (int k = 1; k < nr_vars; k++) {
            for (int j = 0; j < k; j++) {
                ++nr_branches;
                starting_points.push_back(std::make_pair(j, k));
            }
        }
        printf("Nr. root branches: %d\n", nr_branches);
        if (nr_branches > nr_threads) {
            printf("Error: unable to distribute %d branches over %d "
                    "threads\n", nr_branches, nr_threads);
            return dags;
        }

        std::mutex vmutex;
        
        for (int i = 0; i < starting_points.size(); i++) {
            const auto& sp = starting_points[i];
            threads.push_back(
                std::thread([i, &dags, &vmutex, &sp, nr_vars, nr_vertices] {
                    printf("Starting thread %d\n", i+1);

                    rec_dag_generator gen;
                    gen.reset(nr_vars, nr_vertices);
                    gen.add_selection(sp.first, sp.second);
                    auto tdags = gen.gen_dags();
                    {
                        std::lock_guard<std::mutex> vlock(vmutex);
                        for (auto& dag : tdags) {
                            dags.push_back(dag);
                        }
                    }
                }
            ));
        }

        for (auto& t : threads) {
            t.join();
        }

        printf("Generated %lu dags\n", dags.size());

        return dags;
    }


}

