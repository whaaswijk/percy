#include <percy/percy.hpp>
#include <cassert>

void test_aig_from_constant()
{
  percy::chain c;
  percy::spec spec;
  spec.set_primitive( percy::AIG );

  kitty::dynamic_truth_table tt{2};

  /* constant false */
  spec[0] = tt;

  auto result = percy::synthesize( spec, c );
  assert( result == percy::success );
  assert( c.get_nr_steps() == 0 );
  assert( c.simulate()[0] == spec[0] );
  assert( c.is_aig() );

  /* constant true */
  spec[0] = ~tt;

  result = percy::synthesize( spec, c );
  assert( result == percy::success );
  assert( c.get_nr_steps() == 0 );
  assert( c.simulate()[0] == spec[0] );
  assert( c.is_aig() );
}

void test_aig_from_variable()
{
  percy::chain c;
  percy::spec spec;
  spec.set_primitive( percy::AIG );

  kitty::dynamic_truth_table a{2};
  kitty::dynamic_truth_table b{2};

  /* variable a */
  spec[0] = a;

  auto result = percy::synthesize( spec, c );
  assert( result == percy::success );
  assert( c.get_nr_steps() == 0 );
  assert( c.simulate()[0] == spec[0] );
  assert( c.is_aig() );

  /* variable b */
  spec[0] = b;

  result = percy::synthesize( spec, c );
  assert( result == percy::success );
  assert( c.get_nr_steps() == 0 );
  assert( c.simulate()[0] == spec[0] );
  assert( c.is_aig() );

  /* negated variable a */
  spec[0] = ~a;

  result = percy::synthesize( spec, c );
  assert( result == percy::success );
  assert( c.get_nr_steps() == 0 );
  assert( c.simulate()[0] == spec[0] );
  assert( c.is_aig() );

  /* negated variable b */
  spec[0] = ~b;

  result = percy::synthesize( spec, c );
  assert( result == percy::success );
  assert( c.get_nr_steps() == 0 );
  assert( c.simulate()[0] == spec[0] );
  assert( c.is_aig() );
}

void test_aig_from_two_input_function()
{
  percy::chain c;
  percy::spec spec;
  spec.set_primitive( percy::AIG );

  kitty::dynamic_truth_table a{2};
  kitty::dynamic_truth_table b{2};
  kitty::create_nth_var( a, 0 );
  kitty::create_nth_var( b, 1 );

  /* AND */
  spec[0] = a & b;
  auto result = percy::synthesize( spec, c );
  assert( result == percy::success );
  assert( c.get_nr_steps() == 1 );
  assert( c.simulate()[0] == spec[0] );
  assert( c.is_aig() );

  spec[0] = ~a & b;
  result = percy::synthesize( spec, c );
  assert( result == percy::success );
  assert( c.get_nr_steps() == 1 );
  assert( c.simulate()[0] == spec[0] );
  assert( c.is_aig() );

  spec[0] = a & ~b;
  result = percy::synthesize( spec, c );
  assert( result == percy::success );
  assert( c.get_nr_steps() == 1 );
  assert( c.simulate()[0] == spec[0] );
  assert( c.is_aig() );

  spec[0] = ~a & ~b;
  result = percy::synthesize( spec, c );
  assert( result == percy::success );
  assert( c.get_nr_steps() == 1 );
  assert( c.simulate()[0] == spec[0] );
  assert( c.is_aig() );

  spec[0] = ~( a &  b );
  result = percy::synthesize( spec, c );
  assert( result == percy::success );
  assert( c.get_nr_steps() == 1 );
  assert( c.simulate()[0] == spec[0] );
  assert( c.is_aig() );

  /* OR */
  spec[0] = a | b;
  result = percy::synthesize( spec, c );
  assert( result == percy::success );
  assert( c.get_nr_steps() == 1 );
  assert( c.simulate()[0] == spec[0] );
  assert( c.is_aig() );

  spec[0] = ~a | b;
  result = percy::synthesize( spec, c );
  assert( result == percy::success );
  assert( c.get_nr_steps() == 1 );
  assert( c.simulate()[0] == spec[0] );
  assert( c.is_aig() );

  spec[0] = a | ~b;
  result = percy::synthesize( spec, c );
  assert( result == percy::success );
  assert( c.get_nr_steps() == 1 );
  assert( c.simulate()[0] == spec[0] );
  assert( c.is_aig() );

  spec[0] = ~a | ~b;
  result = percy::synthesize( spec, c );
  assert( result == percy::success );
  assert( c.get_nr_steps() == 1 );
  assert( c.simulate()[0] == spec[0] );
  assert( c.is_aig() );

  spec[0] = ~( a | b );
  result = percy::synthesize( spec, c );
  assert( result == percy::success );
  assert( c.get_nr_steps() == 1 );
  assert( c.simulate()[0] == spec[0] );
  assert( c.is_aig() );

  /* XOR */
  spec[0] = a ^ b;
  result = percy::synthesize( spec, c );
  assert( result == percy::success );
  assert( c.get_nr_steps() == 3 );
  assert( c.simulate()[0] == spec[0] );
  assert( c.is_aig() );

  spec[0] = ~a ^ b;
  result = percy::synthesize( spec, c );
  assert( result == percy::success );
  assert( c.get_nr_steps() == 3 );
  assert( c.simulate()[0] == spec[0] );
  assert( c.is_aig() );

  spec[0] = a ^ ~b;
  result = percy::synthesize( spec, c );
  assert( result == percy::success );
  assert( c.get_nr_steps() == 3 );
  assert( c.simulate()[0] == spec[0] );
  assert( c.is_aig() );

  spec[0] = ~a ^ ~b;
  result = percy::synthesize( spec, c );
  assert( result == percy::success );
  assert( c.get_nr_steps() == 3 );
  assert( c.simulate()[0] == spec[0] );
  assert( c.is_aig() );

  spec[0] = ~( a ^ b );
  result = percy::synthesize( spec, c );
  assert( result == percy::success );
  assert( c.get_nr_steps() == 3 );
  assert( c.simulate()[0] == spec[0] );
  assert( c.is_aig() );
}

void test_aig_from_three_input_xor()
{
  percy::chain chain;
  percy::spec spec;
  spec.set_primitive( percy::AIG );

  kitty::dynamic_truth_table a{3};
  kitty::dynamic_truth_table b{3};
  kitty::dynamic_truth_table c{3};
  kitty::create_nth_var( a, 0 );
  kitty::create_nth_var( b, 1 );
  kitty::create_nth_var( c, 2 );

  spec[0] = a ^ b ^ c;

  auto result = percy::synthesize( spec, chain );
  assert( result == percy::success );
  assert( chain.get_nr_steps() == 6 );
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
