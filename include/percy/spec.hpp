#pragma once

#include <chrono>
#include "tt_utils.hpp"

#define MAX_OUT 64 // The maximum supported number of outputs

namespace percy
{
    template<typename TT>
    class synth_spec
    {
        private:
            int nr_in; ///< The number of inputs to the function 
            int tt_size; ///< The size of the truth table
            int nr_out; ///< The number of outputs to synthesize

        public:
            int nr_steps; ///< The number of Boolean operators to use
            int verbosity = 0; ///< Verbosity level for debugging purposes
            uint64_t out_inv; ///< Is 1 at index i if output i must be inverted
            uint64_t triv_flag; ///< Is 1 at index i if output i is constant zero or one or a projection.
            int nr_triv; ///< Number of trivial output functions
            int nr_nontriv; ///< Number of non-trivial output functions
            int nr_rand_tt_assigns; ///< Number of truth table bits to assign randomly in CEGAR loop

            bool add_nontriv_clauses = true; ///< Symmetry break: do not allow trivial operators
            bool add_alonce_clauses = true; ///< Symmetry break: all steps must be used at least once
            bool add_noreapply_clauses = true; ///< Symmetry break: no re-application of operators
            bool add_colex_clauses = true; ///< Symmetry break: order step fanins co-lexicographically
            bool add_lex_func_clauses = true; ///< Symmetry break: order step operators co-lexicographically
            bool add_symvar_clauses = true; ///< Symmetry break: impose order on symmetric variables
            bool add_lex_clauses = false; ///< Symmetry break: order step fanins lexicographically

            const TT* functions[MAX_OUT]; ///< The functions to synthesize
            int triv_functions[MAX_OUT]; ///< Trivial outputs
            int synth_functions[MAX_OUT]; ///< Nontrivial outputs

            /// A place for synthesizers to log elapsed synthesis time.
            /// Measured in microseconds.
            int64_t synth_time;
  
            /// Limit on the number of SAT conflicts. Zero means no limit.
            int conflict_limit = 0;
            
            /// Default constructor leaves default settings untouched.
            synth_spec() { }

            /// Construct a spec with nr_in inputs and nr_out outputs.
            synth_spec(int nr_in, int nr_out)
            {
                set_nr_in(nr_in);
                set_nr_out(nr_out);
            }

            void
            set_nr_in(const int n)
            {
                nr_in = n;
                tt_size = (1 << nr_in) - 1;
            }

            void
            set_nr_out(const int n)
            {
                assert(n <= MAX_OUT);
                nr_out = n;
            }

            int get_nr_in() const { return nr_in; }
            int get_tt_size() const { return tt_size; }
            int get_nr_out() const { return nr_out; }

            /// Normalizes outputs by converting them to normal functions. Also
            /// checks for trivial outputs, such as constant functions or
            /// projections. This determines which of the specifeid functions
            /// need to be synthesized.  This function expects the following
            /// invariants to hold:
            /// 1. The number of input variables has been set.
            /// 2. The number of output variables has been set.
            /// 3. The functions requested to be synthesized have been set.
            void 
            preprocess(void)
            {
                if (verbosity) {
                    printf("\n");
                    printf("========================================"
                            "========================================\n");
                    printf("  Pre-processing for %s:\n", nr_out > 1 ? 
                            "functions" : "function");
                    for (int h = 0; h < nr_out; h++) {
                        printf("  ");
                        kitty::print_binary(*functions[h], std::cout);
                        printf("\n");
                    }
                    printf("========================================"
                            "========================================\n");
                    printf("  SPEC:\n");
                    printf("\tnr_in=%d\n", nr_in);
                    printf("\tnr_out=%d\n", nr_out);
                    printf("\ttt_size=%d\n", tt_size);
                }

                assert((!add_colex_clauses && !add_lex_clauses) ||
                        (add_colex_clauses != add_lex_clauses));

                // Detect any trivial outputs.
                nr_triv = 0;
                nr_nontriv = 0;
                out_inv = 0;
                triv_flag = 0;
                for (int h = 0; h < nr_out; h++) {
                    if (is_const0(*functions[h])) {
                        triv_flag |= (1 << h);
                        triv_functions[nr_triv++] = 0;
                    } else if (is_const0(~(*functions[h]))) {
                        triv_flag |= (1 << h);
                        triv_functions[nr_triv++] = 0;
                        out_inv |= (1 << h);
                    } else {
                        auto tt_var = functions[0]->construct();
                        for (int i = 0; i < nr_in; i++) {
                            create_nth_var(tt_var, i);
                            if (*functions[h] == tt_var) {
                                triv_flag |= (1 << h);
                                triv_functions[nr_triv++] = i+1;
                                break;
                            } else if (*functions[h] == ~(tt_var)) {
                                triv_flag |= (1 << h);
                                triv_functions[nr_triv++] = i+1;
                                out_inv |= (1 << h);
                                break;
                            }
                        }
                        // Even when the output is not trivial, we still need
                        // to ensure that it's normal.
                        if (!((triv_flag >> h) & 1)) {
                            if (!is_normal(*functions[h])) {
                                out_inv |= (1 << h);
                            }
                            synth_functions[nr_nontriv++] = h;
                        }
                    }
                }

                if (verbosity) {
                    for (int h = 0; h < nr_out; h++) {
                        if ((triv_flag >> h) & 1) {
                            printf("  Output %d is trivial\n", h+1);
                        }
                        if ((out_inv >> h) & 1) {
                            printf("  Inverting output %d\n", h+1);
                        }
                    }
                    printf("  Trivial outputs=%d\n", nr_triv);
                    printf("  Non-trivial outputs=%d\n", nr_out-nr_triv);
                    printf("========================================"
                            "========================================\n");
                    printf("\n");
                }
            }

    };

}

