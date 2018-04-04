#pragma once

#include "base/abc/abc.h"
#include "misc/vec/vecInt.h"
#include "misc/vec/vecPtr.h"
#include "sat/bsat/satSolver.h"
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
#include "spec.hpp"
#include "synthesizers.hpp"
#include <kitty/kitty.hpp>


using abc::lit;
using abc::sat_solver;

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

    static inline bool is_trivial(const kitty::dynamic_truth_table& tt)
    {
        kitty::dynamic_truth_table tt_check(tt.num_vars());

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

    /*
    template<typename TT>
    static inline int 
    get_sim_var(const synth_spec<TT>& spec, int i, int t)
    {
        assert(i < spec.nr_steps);
        assert(t < spec.nr_sim_vars );

        return spec.sim_offset + spec.tt_size * i + t;
    }

    template<typename TT>
    static inline int 
    get_out_var(const synth_spec<TT>& spec, int h, int i)
    {
        assert(h < spec.nr_nontriv);
        assert(i < spec.nr_steps);

        return spec.out_offset + spec.nr_steps * h + i;
    }

    template<typename TT>
    static inline int
    get_op_var(const synth_spec<TT>& spec, int i, int c, int b)
    {
        assert(i < spec.nr_steps);
        assert(b < 2 );
        assert(c < 2 );
        assert(b > 0 || c > 0);

        return spec.steps_offset + i * 3 + ( c << 1 ) + b - 1;
    }

    template<typename TT>
    static inline int
    get_op_var(const synth_spec<TT>& spec, int i, int d, int c, int b)
    {
        assert(i < spec.nr_steps);
        assert(b < 2 );
        assert(c < 2 );
        assert(d < 2 );
        assert(b > 0 || c > 0 || d > 0);

        return spec.steps_offset + i * 7 + (d << 2) + ( c << 1 ) + b - 1;
    }

    template<typename TT>
    static inline int
    get_sel_var(const synth_spec<TT>& spec, int i, int j, int k)
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

    template<typename TT>
    static inline int
    get_sel_var(const synth_spec<TT>& spec, int i, int j, int k, int l)
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
    */

    template<typename TT>
    static inline int
    get_fence_var(const synth_spec<TT>& spec, int idx)
    {
        return spec.fence_offset + idx;
    }

    /*
    template<typename Solver>
    void spec_preprocess(synth_spec<dynamic_truth_table>& spec) 
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
    

    template<typename T, typename TT>
    synth_result 
    chain_exists(T* synth, synth_spec<TT>& spec)
    {
        if (spec.verbosity) {
            printf("  Existence check with %d steps...\n", spec.nr_steps);
        }

        synth->restart_solver();
        synth->add_clauses(spec);

        auto status = synth->solve(spec.conflict_limit);

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

    template<typename T, typename TT>
    synth_result 
    cegar_chain_exists(
            T* synth, synth_spec<TT>& spec, chain<TT,2>& chain)
    {
        if (spec.verbosity) {
            printf("  Existence check with %d steps...\n", spec.nr_steps);
        }

        synth->restart_solver();
        synth->cegar_add_clauses(spec);
        for (int i = 0; i < spec.nr_rand_tt_assigns; i++) {
            if (!synth->create_tt_clauses(spec, rand() % spec.tt_size)) {
                return failure;
            }
        }

        while (true) {
            auto status = synth->solve(spec.conflict_limit);
            if (status == success) {
                if (spec.verbosity > 1) {
                    synth->print_solver_state(spec);
                }
                synth->chain_extract(spec, chain);
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
                if (!synth->create_tt_clauses(spec, first_one-1)) {
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
*/


    /***************************************************************************
        A parallel version which periodically checks if a solution has been
        found by another thread.
    template<typename T, typename TT>
    synth_result 
    pcegar_chain_exists(
            T* synth, synth_spec<TT>& spec, chain<2>& chain,
            bool* found)
    {
        if (spec.verbosity) {
            printf("  Existence check with %d steps...\n", spec.nr_steps);
        }

        synth->restart_solver();
        synth->cegar_add_clauses(spec);
        for (int i = 0; i < spec.nr_rand_tt_assigns; i++) {
            if (!synth->create_tt_clauses(spec, rand() % spec.tt_size)) {
                return failure;
            }
        }

        while (true) {
            auto status = synth->solve(spec.conflict_limit);
            if (status == success) {
                if (spec.verbosity > 1) {
                    synth->print_solver_state(spec);
                }
                synth->chain_extract(spec, chain);
                auto sim_tts = chain.simulate<TT>();
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
                if (!synth->create_tt_clauses(spec, first_one-1)) {
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
    ***************************************************************************/

    /***************************************************************************
        The following are constructor functions that allocate new synthesizer
        objects. This is the preferred way of instantiating new synthesizers.
    ***************************************************************************/
    template<int FI=2, typename E=knuth_encoder<FI>, typename S=sat_solver*>
    auto
    new_std_synth()
    {
        return std::make_unique<std_synthesizer<FI, E, S>>();
    }

    template<int FI=2, typename E=fence_encoder<FI>, typename S=sat_solver*>
    auto
    new_fence_synth()
    {
        return std::make_unique<fence_synthesizer<FI, E, S>>();
    }

    template<int FI=2, typename E=dag_encoder<dag<FI>>, typename S=sat_solver*>
    auto
    new_dag_synth()
    {
        return std::make_unique<dag_synthesizer<FI, E, S>>();
    }

    /*
    template<typename TT, typename Solver, typename Generator>
    void
    fence_synthesize_parallel(
            const synth_spec<TT>& main_spec, chain<2>& chain, 
            synth_result& result, bool& stop, Generator& gen, 
            std::mutex& gen_mutex)
    {
        // We cannot directly copy the spec. We need each thread to have its
        // own specification and solver to avoid threading issues.
        synth_spec<TT> spec;
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

        spec_preprocess(spec);
        
        // The special case when the Boolean chain to be synthesized consists
        // entirely of trivial functions.
        if (spec.nr_triv == spec.nr_out) {
            chain.reset(spec.nr_in, spec.nr_out, 0);
            for (int h = 0; h < spec.nr_out; h++) {
                chain.set_output(h, (spec.triv_functions[h] << 1) +
                        ((spec.out_inv >> h) & 1));
            }
            std::lock_guard<std::mutex> gen_lock(gen_mutex);
            if (spec.verbosity > 2) {
                printf("Thread %lu SOLUTION(0)\n", std::this_thread::get_id());
            }
            stop = true;
            result = success;
            return;
        }

        auto synth = new_fence_synth();

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
            auto status = chain_exists(synth.get(), spec);
            if (status == success) {
                synth->extract_chain(spec, chain);
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
                total_conflicts += synth->get_nr_conflicts();
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
    cegar_fence_synthesize_parallel(
            const synth_spec<TT>& main_spec, chain<TT>& chain, 
            synth_result& result, bool& stop, Generator& gen, 
            std::mutex& gen_mutex)
    {
        // We cannot directly copy the spec. We need each thread to have its own
        // specification and solver to avoid threading issues.
        synth_spec<TT> spec;
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

        spec_preprocess(spec);
        spec.nr_rand_tt_assigns = 2*spec.nr_in;
        
        // The special case when the Boolean chain to be synthesized consists
        // entirely of trivial functions.
        if (spec.nr_triv == spec.nr_out) {
            chain.reset(spec.nr_in, spec.nr_out, 0);
            for (int h = 0; h < spec.nr_out; h++) {
                chain.set_output(h, (spec.triv_functions[h] << 1) +
                        ((spec.out_inv >> h) & 1));
            }
            std::lock_guard<std::mutex> gen_lock(gen_mutex);
            if (spec.verbosity > 2) {
                printf("Thread %lu SOLUTION(0)\n", std::this_thread::get_id());
            }
            stop = true;
            result = success;
            return;
        }

        auto synth = new_synth<fence_synthesizer<TT,Solver>>();

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
            auto status = cegar_chain_exists(synth.get(), spec, chain);
            if (status == success) {
                synth->chain_extract(spec, chain);
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
                total_conflicts += synth->get_nr_conflicts();
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
            const synth_spec<TT>& spec, const int nr_threads, 
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
                    fence_synthesize_parallel<TT, Solver>(spec, c, status, 
                            stop, g, m);
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
            const synth_spec<TT>& spec, const int nr_threads, 
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
                    cegar_fence_synthesize_parallel<TT, Solver>(spec, 
                            c, status, stop, g, m);
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
    */

    /***************************************************************************
        Finds the smallest possible DAG that can implement the specified
        function.
    ***************************************************************************/
    template<typename TT, int FI=2>
    synth_result find_dag(const TT& f, dag<FI>& g, int nr_vars)
    {
        chain<FI> chain;
        rec_dag_generator gen;
        dag_synthesizer<FI> synth;

        synth_spec<TT> spec(nr_vars, 1);
        spec.functions[0] = &f;

        int nr_vertices = 1;
        while (true) {
            gen.reset(nr_vars, nr_vertices);
            g.reset(nr_vars, nr_vertices);
            const auto result = gen.find_dag(spec, g, chain, synth);
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
    template<typename TT, int FI=2>
    synth_result 
    find_dag(const TT& f, dag<FI>& g, int nr_vars, int nr_vertices)
    {
        chain<FI> chain;
        rec_dag_generator gen;
        dag_synthesizer<FI> synth;

        gen.reset(nr_vars, nr_vertices);
        g.reset(nr_vars, nr_vertices);
        return gen.find_dag(f, g, chain, synth);
    }



    template<typename TT>
    synth_result 
    qpfind_dag(
            const TT& function, 
            dag<2>& g, 
            int nr_vars,
            bool verbose=false)
    {
        synth_spec<TT> spec(nr_vars, 1);
        spec.functions[0] = &function;

        int nr_vertices = 1;
        while (true) {
            if (verbose) {
                fprintf(stderr, "Trying with %d vertices\n", nr_vertices);
                fflush(stderr);
            }
            const auto status = qpfind_dag<TT>(spec, g, nr_vars, nr_vertices);
            if (status == success) {
                return success;
            }
            nr_vertices++;
        }
        
        return failure;
    }

    template<typename TT, int FI=2>
    synth_result 
    qpfind_dag(
            const synth_spec<TT>& spec, 
            dag<2>& g, 
            int nr_vars, 
            int nr_vertices)
    {
        vector<std::thread> threads;
       
        const auto nr_threads = std::thread::hardware_concurrency() - 1;
        
        moodycamel::ConcurrentQueue<dag<2>> q(nr_threads*3);
        

        bool finished_generating = false;
        bool* pfinished = &finished_generating;
        bool found = false;
        bool* pfound = &found;
        std::mutex found_mutex;

        g.reset(nr_vars, nr_vertices);
        for (int i = 0; i < nr_threads; i++) {
            threads.push_back(
                std::thread([&spec, pfinished, pfound, &found_mutex, &g, 
                            &q, nr_vars, nr_vertices] {
                    dag<2> local_dag;
                    chain<FI> chain;
                    dag_synthesizer<FI> synth;

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
                            synth.synthesize(spec, local_dag, chain);

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
            dag<2> local_dag;
            chain<FI> chain;
            dag_synthesizer<FI> synth;

            while (!found) {
                if (!q.try_dequeue(local_dag)) {
                    break;
                }
                const auto status = synth.synthesize(spec, local_dag, chain);

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

    template<typename TT, class Dag=dag<2>>
    synth_result 
    qpfence_synth(
            synth_stats* stats,
            const TT& function, 
            Dag& g, 
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

    template<typename TT, int FI=2>
    synth_result 
    qpfence_synth(
            synth_stats* stats,
            const TT& f, 
            dag<FI>& g, 
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
                    chain<FI> chain;
                    fence local_fence;
                    fence_synthesizer<FI> synth;

                    synth_spec<TT> local_spec(nr_vars, 1);
                    local_spec.verbosity = 0;
                    local_spec.nr_steps = nr_vertices;
                    local_spec.functions[0] = &f;
                    local_spec.nr_rand_tt_assigns = 2 * local_spec.get_nr_in();
                    local_spec.conflict_limit = conflict_limit;

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

                        auto status = synth.cegar_synthesize(local_spec,
                                local_fence, chain);

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
            chain<FI> chain;
            fence local_fence;
            fence_synthesizer<FI> synth;

            synth_spec<TT> local_spec(nr_vars, 1);
            local_spec.verbosity = 0;
            local_spec.nr_steps = nr_vertices;
            local_spec.functions[0] = &f;
            local_spec.nr_rand_tt_assigns = 2 * local_spec.get_nr_in();
            local_spec.conflict_limit = conflict_limit;

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

                auto status = synth.cegar_synthesize(local_spec, local_fence,
                        chain);

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
        vector<std::pair<int,int>> starting_points;
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

    vector<dag<2>> 
    parallel_dag_gen(int nr_vars, int nr_vertices, int nr_threads)
    {
        printf("Initializing %d-thread parallel DAG gen\n", nr_threads);
        printf("nr_vars=%d, nr_vertices=%d\n", nr_vars, nr_vertices);
        vector<std::thread> threads;

        // Each thread will write the DAGs it has found to this vector.
        vector<dag<2>> dags;

        // First estimate the number of solutions down each branch by looking
        // at DAGs with small numbers of vertices.
        int nr_branches = 0;
        vector<std::pair<int,int>> starting_points;
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

