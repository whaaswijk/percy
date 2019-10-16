#include <percy/percy.hpp>
#include <cassert>

void test_simple()
{
  percy::chain chain;
  percy::spec spec;
  spec.verbosity = 1;

  /* specify local normalized gate primitives */
  kitty::dynamic_truth_table a{2};
  kitty::dynamic_truth_table b{2};
  kitty::create_nth_var( a, 0 );
  kitty::create_nth_var( b, 1 );
  spec.add_primitive(  a &  b ); //  a AND  b
  spec.add_primitive( ~a &  b ); // ~a AND  b
  spec.add_primitive(  a & ~b ); //  a AND ~b
  spec.add_primitive(  a |  b ); //  a  OR  b

  kitty::dynamic_truth_table x{3};
  kitty::dynamic_truth_table y{3};
  kitty::dynamic_truth_table z{3};
  kitty::create_nth_var( x, 0 );
  kitty::create_nth_var( y, 1 );

  /* add some additional normalized functions */
  spec.add_function( ~x &  y );
  spec.add_function(  x & ~y );

  /* xor */
  spec[0] = x ^ y;

  auto const result = percy::synthesize( spec, chain );
  assert( result == percy::success );

  auto const sim = chain.simulate();
  assert( chain.simulate()[0] == spec[0] );

  /* now we only need one more step because we start with the two
     functions ( ~x & y ) and ( x & ~y ) */
  assert( chain.get_nr_steps() == 1u );
}

int main()
{
  test_simple();
}
