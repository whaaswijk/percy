#include <percy/percy.hpp>
#include <cassert>
#include <cstdio>
#include <fstream>

using namespace percy;
using kitty::dynamic_truth_table;

/*******************************************************************************
    Tests the generation of multiple solutions from a single specification
    and ensure that the number of solutions is the same between different
    encodings.
*******************************************************************************/
int main(void)
{
    
    {
        spec spec;
        spec.verbosity = 0;

        bsat_wrapper solver;
        ssv_encoder enc_ssv(solver);
        msv_encoder enc_msv(solver);
        ditt_encoder enc_ditt(solver);
        chain c;

        dynamic_truth_table tt2(2);

        for (int i = 0; i < 16; i++) {
            kitty::create_from_words(tt2, &i, &i+1);
            spec[0] = tt2;

            //printf("Generating solutions for function ");
            //kitty::print_binary(tt2);
            //printf("\n");

            enc_ssv.reset();
            enc_msv.reset();
            enc_ditt.reset();
            auto solutions1 = 0;
            while (next_solution(spec, c, solver, enc_ssv) == success) {
                assert(c.get_nr_steps() <= 1);

                //printf("Next solution: ");
                //c.to_expression(std::cout);
                //printf("\n");

                assert(c.satisfies_spec(spec));
                solutions1++;
            }

            auto solutions2 = 0;
            while (next_solution(spec, c, solver, enc_msv) == success) {
                assert(c.get_nr_steps() <= 1);

                //printf("Next solution: ");
                //c.to_expression(std::cout);
                //printf("\n");

                assert(c.satisfies_spec(spec));
                solutions2++;
            }

            auto solutions3 = 0;
            while (next_solution(spec, c, solver, enc_ditt) == success) {
                assert(c.get_nr_steps() <= 1);

                //printf("Next solution: ");
                //c.to_expression(std::cout);
                //printf("\n");

                assert(c.satisfies_spec(spec));
                solutions3++;
            }
            assert(solutions1 == solutions2);
            assert(solutions2 == solutions3);
        }

        dynamic_truth_table tt3(3);
        for (int i = 0; i < 256; i++) {
            kitty::create_from_words(tt3, &i, &i+1);
            spec[0] = tt3;

            //printf("Generating solutions for function ");
            //kitty::print_binary(tt3);
            //printf("\n");

            enc_ssv.reset();
            enc_msv.reset();
            enc_ditt.reset();
            auto solutions1 = 0;
            //printf("=== SYNTH 1 ===\n");
            while (next_solution(spec, c, solver, enc_ssv) == success) {
                //printf("Next solution: ");
                //c.to_expression(std::cout);
                //printf("\n");
                
                assert(c.satisfies_spec(spec));
                solutions1++;
            }
            auto solutions2 = 0;
            //printf("=== SYNTH 2 ===\n");
            while (next_solution(spec, c, solver, enc_msv) == success) {
                //printf("Next solution: ");
                //c.to_expression(std::cout);
                //printf("\n");
                
                assert(c.satisfies_spec(spec));
                solutions2++;
            }

            auto solutions3 = 0;
            //printf("=== SYNTH 3 ===\n");
            while (next_solution(spec, c, solver, enc_ditt) == success) {
                //printf("Next solution: ");
                //c.to_expression(std::cout);
                //printf("\n");
                
                assert(c.satisfies_spec(spec));
                solutions3++;
            }

            assert(solutions1 == solutions2);
            assert(solutions2 == solutions3);
        }

        spec.fanin = 3;
        
        dynamic_truth_table tt4(4);
        for (int i = 0; i < 256; i++) {
            kitty::create_from_words(tt4, &i, &i+1);
            spec[0] = tt4;

            //printf("Generating solutions for function ");
            //kitty::print_binary(tt4);
            //printf("\n");

            enc_ssv.reset();
            enc_msv.reset();
            enc_ditt.reset();
            auto solutions1 = 0;
            while (next_solution(spec, c, solver, enc_ssv) == success) {
                //printf("Next solution: (%d vertices)\n", c.get_nr_steps());
                assert(c.satisfies_spec(spec));
                solutions1++;
            }

            auto solutions2 = 0;
            while (next_solution(spec, c, solver, enc_msv) == success) {
                //printf("Next solution: (%d vertices)\n", c.get_nr_steps());
                assert(c.satisfies_spec(spec));
                solutions2++;
            }

            auto solutions3 = 0;
            while (next_solution(spec, c, solver, enc_ditt) == success) {
                //printf("Next solution: (%d vertices)\n", c.get_nr_steps());
                assert(c.satisfies_spec(spec));
                solutions3++;
            }

            assert(solutions1 == solutions2);
            assert(solutions2 == solutions3);
        }
    }
    
    return 0;
}

