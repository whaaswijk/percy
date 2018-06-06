#include <percy/percy.hpp>
#include <kitty/kitty.hpp>
#include <cassert>
#include <cstdio>
#include <fstream>

using namespace percy;
using kitty::static_truth_table;

/*******************************************************************************
    Tests the generation of multiple solutions from a single specification
    and ensure that the number of solutions is the same between different
    encodings.
*******************************************************************************/
int main(void)
{
    
    {
        synth_spec<static_truth_table<2>> spec2(2, 1);
        spec2.verbosity = 0;

        auto synth1 = new_std_synth();
        auto synth2 = new_std_synth<2, abc::sat_solver*, epfl_encoder<2, abc::sat_solver*>>();
        chain<2> c;

        static_truth_table<2> tt2;

        for (int i = 0; i < 16; i++) {
            kitty::create_from_words(tt2, &i, &i+1);
            spec2.functions[0] = &tt2;

            printf("Generating solutions for function ");
            kitty::print_binary(tt2);
            printf("\n");

            synth1->reset();
            synth2->reset();
            auto solutions1 = 0;
            while (synth1->next_solution(spec2, c) == success) {
                assert(c.get_nr_vertices() <= 1);

                printf("Next solution: ");
                c.to_expression(std::cout);
                printf("\n");

                assert(c.satisfies_spec(spec2));
                solutions1++;
            }

            auto solutions2 = 0;
            while (synth2->next_solution(spec2, c) == success) {
                assert(c.get_nr_vertices() <= 1);

                printf("Next solution: ");
                c.to_expression(std::cout);
                printf("\n");

                assert(c.satisfies_spec(spec2));
                solutions2++;
            }
            assert(solutions1 == solutions2);
        }

        synth_spec<static_truth_table<3>> spec3(3, 1);
   
        static_truth_table<3> tt3;

        for (int i = 0; i < 256; i++) {
            kitty::create_from_words(tt3, &i, &i+1);
            spec3.functions[0] = &tt3;

            printf("Generating solutions for function ");
            kitty::print_binary(tt3);
            printf("\n");

            synth1->reset();
            auto solutions1 = 0;
            printf("=== SYNTH 1 ===\n");
            while (synth1->next_solution(spec3, c) == success) {
                printf("Next solution: ");
                c.to_expression(std::cout);
                printf("\n");
                
                assert(c.satisfies_spec(spec3));
                solutions1++;
            }
            synth2->reset();
            auto solutions2 = 0;
            printf("=== SYNTH 2 ===\n");
            while (synth2->next_solution(spec3, c) == success) {
                printf("Next solution: ");
                c.to_expression(std::cout);
                printf("\n");
                
                assert(c.satisfies_spec(spec3));
                solutions2++;
            }

            assert(solutions1 == solutions2);
        }

        auto synth31 = new_std_synth<3>();
        auto synth32 = new_std_synth<3, abc::sat_solver*, epfl_encoder<3, abc::sat_solver*>>();
        chain<3> c3;
        synth_spec<static_truth_table<4>> spec4(4, 1);
        
        static_truth_table<4> tt4;

        for (int i = 0; i < 256; i++) {
            kitty::create_from_words(tt4, &i, &i+1);
            spec4.functions[0] = &tt4;

            printf("Generating solutions for function ");
            kitty::print_binary(tt4);
            printf("\n");

            synth31->reset();
            auto solutions1 = 0;
            while (synth31->next_solution(spec4, c3) == success) {
                printf("Next solution: (%d vertices)\n", c3.get_nr_vertices());
                assert(c3.satisfies_spec(spec4));
                solutions1++;
            }

            synth32->reset();
            auto solutions2 = 0;
            while (synth32->next_solution(spec4, c3) == success) {
                printf("Next solution: (%d vertices)\n", c3.get_nr_vertices());
                assert(c3.satisfies_spec(spec4));
                solutions2++;
            }

            assert(solutions1 == solutions2);
        }
    }
    
    return 0;
}

