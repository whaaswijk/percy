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
                auto sim_fs = c.simulate(spec2);
                assert(c.get_nr_vertices() <= 1);
                assert(sim_fs[0] == tt2);

                printf("Next solution: ");
                c.to_expression(std::cout);
                printf("\n");
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
                auto sim_fs = c.simulate(spec3);
                assert(sim_fs[0] == tt3);

                printf("Next solution: ");
                c.to_expression(std::cout);
                printf("\n");
            }
        }

        /*
        spec2.set_nr_out(2);
        for (int i = 0; i < 16; i++) {
            kitty::create_from_words(tt2, &i, &i+1);
            spec2.functions[0] = &tt2;
            for (int j = 0; j < 16; j++) {
                kitty::create_from_words(ttj, &j, &j+1);
                spec2.functions[1] = &ttj;
                auto result = synth->synthesize(spec2, c);
                assert(result == success);
                auto sim_fs = c.simulate(spec2);
                assert(c.get_nr_vertices() <= 2);
                assert(sim_fs[0] == tt2);
                assert(sim_fs[1] == ttj);
            }
        }
        */
    }
    
    /*
    // Synthesize a full adder
    {
        synth_spec2<static_truth_table<3>> spec2(3, 2);
        spec2.verbosity = 1;
        auto synth = new_std_synth();
        chain<2> c;

        static_truth_table<3> x, y, z;

        create_nth_var( x, 0 );
        create_nth_var( y, 1 );
        create_nth_var( z, 2 );

        const auto sum = x ^ y ^ z;
        const auto carry = ternary_majority(x, y, z);
        spec2.functions[0] = &sum;
        spec2.functions[1] = &carry;
        auto result = synth->synthesize(spec2, c);
        assert(result == success);
        auto sim_fs = c.simulate(spec2);
        assert(sim_fs[0] == sum);
        assert(sim_fs[1] == carry);
    }
    */

    {
      /*
       * arbiter example
       *
       * inputs:
       * - request by client #1: r1
       * - request by client #2: r2
       * - two state bits for the current state: s2 s1
       *
       * outputs:
       * - access granted to client #1: g1
       * - access granted to client #2: g2
       * - two state bits for the next state: s2_next, s1_next
       */

      /* truth tables of the grant siganls g1 and g2 of a round robin arbiter */
      const std::string g2_tt = "0000" "0000" "1111" "0100";
      const std::string g1_tt = "0000" "1111" "0000" "1010";

      chain<2> c;

      /* enumerate mutants *
      for ( auto i = 4u; i < g1_tt.size(); ++i )
      {
        synth_spec2<static_truth_table<4>,sat_solver*> spec2;
        spec2.nr_in = 4;
        spec2.nr_out = 4;
        spec2.verbosity = 1;
        // simple_synthesizer<static_truth_table<4>,sat_solver*> synth;
        symmetric_synthesizer<static_truth_table<4>,sat_solver*> synth;

        static_truth_table<4> s2, s1, r2, r1, s2_next, s1_next, g2, g1;
        create_nth_var( r1, 0 );
        create_nth_var( r2, 1 );
        create_nth_var( s1, 2 );
        create_nth_var( s2, 3 );

        /* copy the output signal *
        auto g2_tt_copy = g2_tt;
        auto g1_tt_copy = g1_tt;

        /*
         * inject errors into the output signals (violates the
         * property never two grants at the same time)
         *
        g1_tt_copy[i] = '1';
        g2_tt_copy[i] = '1';

        /* next-state logic *
        create_from_binary_string( s2_next, "1111" "0000" "1010" "0000" );
        create_from_binary_string( s1_next, "1111" "1100" "0000" "1000" );

        /* output logic *
        create_from_binary_string( g2, g2_tt_copy );
        create_from_binary_string( g1, g1_tt_copy );

        spec2.functions[0] = &s2_next;
        spec2.functions[1] = &s1_next;
        spec2.functions[2] = &g2;
        spec2.functions[3] = &g1;

        synth.synthesize(spec2, c);
        auto sim_fs = c.simulate();
        assert( sim_fs[0] == s2_next );
        assert( sim_fs[1] == s1_next );
        assert( sim_fs[2] == g2 );
        assert( sim_fs[3] == g1 );
      }
      */
    }

    return 0;
}

