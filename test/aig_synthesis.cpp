#include <percy/percy.hpp>
#include <cassert>

void test_ele_simple()
{
  percy::chain chain;
  percy::spec spec;
  spec.verbosity = 10;
  // spec.set_primitive( percy::AIG );

  kitty::dynamic_truth_table a{3};
  kitty::dynamic_truth_table b{3};
  kitty::dynamic_truth_table c{3};
  kitty::create_nth_var( a, 0 );
  kitty::create_nth_var( b, 1 );
  kitty::create_nth_var( c, 2 );
  spec.add_primitive( a );
  spec.add_primitive( b );
  spec.add_primitive( c );
  spec.add_primitive( kitty::ternary_majority( a, b, c ) );
  spec.add_primitive( kitty::ternary_majority( ~a, b, c ) );
  spec.add_primitive( kitty::ternary_majority( a, ~b, c ) );
  spec.add_primitive( kitty::ternary_majority( a, b, ~c ) );

  kitty::dynamic_truth_table x1{4};
  kitty::dynamic_truth_table x2{4};
  kitty::dynamic_truth_table x3{4};
  kitty::dynamic_truth_table x4{4};
  
  /* AND */
  kitty::dynamic_truth_table const0{4};
  spec[0] = kitty::ternary_majority( x1, x2, kitty::ternary_majority( x3, x4, const0 ) );
  
  auto result = percy::synthesize( spec, chain );
  assert( result == percy::success );
  assert( chain.get_nr_steps() == 6 );
  assert( chain.simulate()[0] == spec[0] );
  assert( chain.is_aig() );
}

void test_aig_from_three_input_function()
{
  percy::chain chain;
  percy::spec spec;
  spec.set_primitive( percy::AIG );

  kitty::dynamic_truth_table tt{3};
  for ( int i = 0; i < 256; ++i )
  {
    kitty::create_from_words( tt, &i, &i + 1 );
    spec[0] = tt;
    auto const result = synthesize( spec, chain );
    assert( result == percy::success );
    assert( chain.is_aig() );
    assert( chain.simulate()[0] == tt );
  }
}

int main(void)
{
  test_aig_from_constant();
  test_aig_from_variable();
  test_aig_from_two_input_function();
  test_aig_from_three_input_xor();
  test_aig_from_three_input_function();
  return 0;
}
