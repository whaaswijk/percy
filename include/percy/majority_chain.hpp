/* percy: C++ exact synthesis library
 * Copyright (C) 2018-2019  EPFL EPFL
 *
 * Permission is hereby granted, free of charge, to any person
 * obtaining a copy of this software and associated documentation
 * files (the "Software"), to deal in the Software without
 * restriction, including without limitation the rights to use,
 * copy, modify, merge, publish, distribute, sublicense, and/or sell
 * copies of the Software, and to permit persons to whom the
 * Software is furnished to do so, subject to the following
 * conditions:
 *
 * The above copyright notice and this permission notice shall be
 * included in all copies or substantial portions of the Software.
 *
 * THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND,
 * EXPRESS OR IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES
 * OF MERCHANTABILITY, FITNESS FOR A PARTICULAR PURPOSE AND
 * NONINFRINGEMENT. IN NO EVENT SHALL THE AUTHORS OR COPYRIGHT
 * HOLDERS BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER LIABILITY,
 * WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING
 * FROM, OUT OF OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR
 * OTHER DEALINGS IN THE SOFTWARE.
 */

/*!
  \file majority_chain.hpp
  \brief Chain of majority-of-three steps

  \author Winston Haaswijk
  \author Heinz Riener
*/

#pragma once
#include <array>

namespace percy
{

class majority_chain;

namespace detail
{
void to_expression( majority_chain const& chain, std::ostream& os, bool write_newline = false );
} /* detail */

/*! \brief Majority chain

  Majority chain is a specialized chain of majority-of-three steps.
*/
class majority_chain
{
public:
  using step = std::array<int32_t, 3u>;

public:
  majority_chain()
  {
    reset( 0, 0, 0 );
  }

  void reset( int32_t new_nr_in, int32_t new_nr_out, int32_t new_nr_steps )
  {
    assert( new_nr_out >= 0 );
    assert( new_nr_steps >= 0 );

    nr_in = new_nr_in;
    steps.resize( new_nr_steps );
    operators.resize( new_nr_steps );
    outputs.resize( new_nr_out );
  }

  /* getter */
  int32_t get_nr_inputs() const
  {
    return nr_in;
  }

  int32_t get_nr_steps() const
  {
    return steps.size();
  }

  /* setter */
  void set_step( int32_t index, int32_t fanin1, int32_t fanin2, int32_t fanin3, int32_t op )
  {
    assert( index >= 0 );
    assert( index < int32_t( steps.size() ) );
    assert( index < int32_t( operators.size() ) );
    steps[index][0] = fanin1;
    steps[index][1] = fanin2;
    steps[index][2] = fanin3;
    operators[index] = op;
  }

  void set_output( int32_t out_index, int32_t lit )
  {
    outputs[out_index] = lit;
  }

  /*! \brief Derive truth tables from the chain, one for each output. */
  std::vector<kitty::dynamic_truth_table> simulate() const
  {
    /* output truth tables */
    std::vector<kitty::dynamic_truth_table> output_tts( outputs.size() );

    /* step truth tables */
    std::vector<kitty::dynamic_truth_table> step_tts( steps.size() );

    /* temporary truth tables of current step's children */
    std::array<kitty::dynamic_truth_table, 3u> child_tts =
      { kitty::dynamic_truth_table{nr_in}, kitty::dynamic_truth_table{nr_in}, kitty::dynamic_truth_table{nr_in} };

    kitty::dynamic_truth_table step_tt{nr_in};

    /* some outputs may be simple constants or projections */
    for ( auto h = 0u; h < outputs.size(); ++h )
    {
      auto const out = outputs[h];
      auto const var = out >> 1;
      auto const inv = out & 1;
      if ( var == 0 )
      {
        kitty::clear( step_tt );
        output_tts[h] = inv ? ~step_tt : step_tt;
      }
      else if ( var <= nr_in )
      {
        kitty::create_nth_var( step_tt, var - 1, inv );
        output_tts[h] = step_tt;
      }
    }

    /* build the truth tables for each step */
    for ( auto i = 0u; i < steps.size(); ++i )
    {
      auto const& step = steps[i];

      for ( auto j = 0u; j < 3; ++j )
      {
        if ( step[j] <= nr_in )
        {
          kitty::create_nth_var( child_tts[j], step[j] - 1 );
        }
        else
        {
          assert( step_tts[step[j] - nr_in - 1].num_vars() == nr_in );
          child_tts[j] = step_tts[step[j] - nr_in - 1];
        }
      }

      kitty::clear( step_tt );
      switch ( operators[i] )
      {
      case 0:
        step_tt = kitty::ternary_majority(  child_tts.at( 0 ),  child_tts.at( 1 ),  child_tts.at( 2 ) );
        break;
      case 1:
        step_tt = kitty::ternary_majority( ~child_tts.at( 0 ),  child_tts.at( 1 ),  child_tts.at( 2 ) );
        break;
      case 2:
        step_tt = kitty::ternary_majority(  child_tts.at( 0 ), ~child_tts.at( 1 ),  child_tts.at( 2 ) );
        break;
      case 3:
        step_tt = kitty::ternary_majority(  child_tts.at( 0 ),  child_tts.at( 1 ), ~child_tts.at( 2 ) );
        break;
      }

      step_tts[i] = step_tt;

      for ( auto h = 0u; h < outputs.size(); ++h )
      {
        const auto out = outputs[h];
        const auto var = out >> 1;
        const auto inv = out & 1;
        if ( var - nr_in - 1 == static_cast<int>(i) ) {
          output_tts[h] = inv ? ~step_tt : step_tt;
        }
      }
    }

    return output_tts;
  }

  /*! \brief Checks if the chain satisfies its specification.
   *
   * This method checks not just if the chain computes the correct
   * function, but also other requirements such as co-lexicographic
   * order (if specified).
   */
  bool satisfies_spec( spec const& spec )
  {
    if (spec.nr_triv == spec.get_nr_out()) {
      return true;
    }
    auto tts = simulate();

    auto nr_nontriv = 0;
    for (int i = 0; i < spec.nr_nontriv; i++) {
      if ((spec.triv_flag >> i) & 1) {
        continue;
      }
      if (tts[nr_nontriv++] != spec[i]) {
        assert(false);
        return false;
      }
    }

    if (spec.add_alonce_clauses) {
      // Ensure that each step is used at least once.
      std::vector<int> nr_uses(steps.size());

      for (auto i = 1u; i < steps.size(); i++) {
        const auto& step = steps[i];
        for (const auto fid : step) {
          if (fid >= nr_in) {
            nr_uses[fid - nr_in]++;
          }
        }
      }
      for (auto output : outputs) {
        const auto step_idx = output >> 1;
        if (step_idx > nr_in) {
          nr_uses[step_idx - nr_in - 1]++;
        }
      }

      for (auto nr : nr_uses) {
        if (nr == 0) {
          assert(false);
          return false;
        }
      }
    }

    if (spec.add_noreapply_clauses) {
      // Ensure there is no re-application of operands.
      for (auto i = 0u; i < steps.size() - 1; i++) {
        const auto & fanins1 = steps[i];
        for (auto ip = i + 1; ip < steps.size(); ip++) {
          const auto& fanins2 = steps[ip];

          auto is_subsumed = true;
          auto has_fanin_i = false;
          for (auto j : fanins2) {
            if (static_cast<unsigned>(j) == i + nr_in) {
              has_fanin_i = true;
              continue;
            }
            auto is_included = false;
            for (auto jp : fanins1) {
              if (j == jp) {
                is_included = true;
              }
            }
            if (!is_included) {
              is_subsumed = false;
            }
          }
          if (is_subsumed && has_fanin_i) {
            assert(false);
            return false;
          }
        }
      }
    }

    if (spec.add_colex_clauses) {
      // Ensure that steps are in STRICT co-lexicographical order.
      for (int i = 0; i < spec.nr_steps - 1; i++) {
        const auto& v1 = steps[i];
        const auto& v2 = steps[i + 1];

        if (colex_compare(v1, v2) != -1) {
          assert(false);
          return false;
        }
      }
    }

    if (spec.add_lex_clauses) {
      // Ensure that steps are in lexicographical order.
      for (int i = 0; i < spec.nr_steps - 1; i++) {
        const auto& v1 = steps[i];
        const auto& v2 = steps[i + 1];

        if (lex_compare(v1, v2) == 1) {
          assert(false);
          return false;
        }
      }
    }

    if (spec.add_lex_func_clauses) {
      // Ensure that step operators are in lexicographical order.
      for (int i = 0; i < spec.nr_steps - 1; i++) {
        const auto& v1 = steps[i];
        const auto& v2 = steps[i + 1];

        if (colex_compare(v1, v2) == 0) {
          // The operator of step i must be lexicographically
          // less than that of i + 1.
          const auto& op1 = operators[i];
          const auto& op2 = operators[i + 1];
          if (op2 > op1) {
            assert(false);
            return false;
          }
        }
      }
    }

    if (spec.add_symvar_clauses) {
      // Ensure that symmetric variables are ordered.
      for (int q = 1; q < spec.get_nr_in(); q++) {
        for (int p = 0; p < q; p++) {
          auto symm = true;
          for (int i = 0; i < spec.get_nr_out(); i++) {
            auto outfunc = spec[i];
            if (!(swap(outfunc, p, q) == outfunc)) {
              symm = false;
              break;
            }
          }
          if (!symm) {
            continue;
          }
          for (int i = 1; i < spec.nr_steps; i++) {
            const auto& v1 = steps[i];
            auto has_fanin_p = false;
            auto has_fanin_q = false;

            for (const auto fid : v1) {
              if (fid == p) {
                has_fanin_p = true;
              } else if (fid == q) {
                has_fanin_q = true;
              }
            }

            if (!has_fanin_q || has_fanin_p) {
              continue;
            }
            auto p_in_prev_step = false;
            for (int ip = 0; ip < i; ip++) {
              const auto& v2 = steps[ip];
              has_fanin_p = false;

              for (const auto fid : v2) {
                if (fid == p) {
                  has_fanin_p = true;
                }
              }
              if (has_fanin_p) {
                p_in_prev_step = true;
              }
            }
            if (!p_in_prev_step) {
              assert(false);
              return false;
            }
          }
        }
      }
    }

    return true;
  }

  /*! \brief Converts the chain to a parseable expression.
   *
   * Currently only supported for single-output chains.
   */
  void to_expression( std::ostream& os, bool write_newline = false ) const
  {
    assert( outputs.size() == 1u );
    detail::to_expression( *this, os, write_newline );
  }

  /*! \brief Converts the chain to a parseable expression.
   *
   * Currently only supported for single-output chains.
   */
  std::string to_expression() const
  {
    assert( outputs.size() == 1u );
    std::stringstream ss;
    detail::to_expression( *this, ss );
    return ss.str();
  }

public:
  int nr_in;
  std::vector<int> outputs;
  std::vector<step> steps;
  std::vector<int> operators;
}; /* majority_chain */

namespace detail
{

void to_expression_recur( majority_chain const& chain, int32_t const index, std::ostream& os )
{
  int32_t const num_inputs = chain.get_nr_inputs();
  if ( index < num_inputs )
  {
    os << static_cast<char>( 'a' + index );
  }
  else
  {
    auto const& step = chain.steps[index - num_inputs];
    os << "<";
    to_expression_recur( chain, step.at( 0 ), os );
    to_expression_recur( chain, step.at( 1 ), os );
    to_expression_recur( chain, step.at( 2 ), os );
    os << ">";
  }
}

void to_expression( majority_chain const& chain, std::ostream& os, bool write_newline )
{
  to_expression_recur( chain, chain.get_nr_inputs() + chain.get_nr_steps() - 1, os );
  if ( write_newline )
    os << '\n';
}
} /* detail */

} /* percy */
