#include <percy/percy.hpp>
#include <kitty/kitty.hpp>
#include <cassert>
#include <cstdio>
#include <fstream>

using namespace percy;
using kitty::static_truth_table;

/*******************************************************************************
    Tests the generation of multiple solutions from a single spec2ification.
*******************************************************************************/
int main(void)
{
    
    {
        synth_spec<static_truth_table<2>> spec2(2, 1);
        spec2.verbosity = 0;

        auto synth = new_std_synth();
        chain<2> c;

        static_truth_table<2> tt2;

        for (int i = 0; i < 16; i++) {
            kitty::create_from_words(tt2, &i, &i+1);
            spec2.functions[0] = &tt2;

            printf("Generating solutions for function ");
            kitty::print_binary(tt2);
            printf("\n");

            synth->reset();
            while (synth->next_solution(spec2, c) == success) {
                assert(c.get_nr_vertices() <= 1);

                printf("Next solution: ");
                c.to_expression(std::cout);
                printf("\n");

                assert(c.satisfies_spec(spec2));
            }
        }

        synth_spec<static_truth_table<3>> spec3(3, 1);
        static_truth_table<3> tt3;

        for (int i = 0; i < 256; i++) {
            kitty::create_from_words(tt3, &i, &i+1);
            spec3.functions[0] = &tt3;

            printf("Generating solutions for function ");
            kitty::print_binary(tt3);
            printf("\n");

            synth->reset();
            while (synth->next_solution(spec3, c) == success) {
                printf("Next solution: ");
                c.to_expression(std::cout);
                printf("\n");
                
                assert(c.satisfies_spec(spec3));
            }
        }

        // Test generating solutions starting from a specified number of steps.
        for (int i = 0; i < 256; i++) {
            kitty::create_from_words(tt3, &i, &i+1);
            spec3.functions[0] = &tt3;

            printf("Generating solutions of size >= 3 for function ");
            kitty::print_binary(tt3);
            printf("\n");

            synth->reset();
            while (synth->next_solution(spec3, c, 3) == success) {
                printf("Next solution: ");
                c.to_expression(std::cout);
                printf("\n");
                
                if (!is_trivial(tt3)) {
                    assert(c.get_nr_vertices() >= 3);
                }
                assert(c.satisfies_spec(spec3));
            }
        }

        auto synth3 = new_std_synth<3>();
        chain<3> c3;
        synth_spec<static_truth_table<4>> spec4(4, 1);
        static_truth_table<4> tt4;

        for (int i = 0; i < 256; i++) {
            kitty::create_from_words(tt4, &i, &i+1);
            spec4.functions[0] = &tt4;

            printf("Generating solutions for function ");
            kitty::print_binary(tt4);
            printf("\n");

            synth3->reset();
            while (synth3->next_solution(spec4, c3) == success) {
                printf("Next solution: (%d vertices)\n", c3.get_nr_vertices());
                assert(c3.satisfies_spec(spec4));
            }
        }
    }
    
    return 0;
}

