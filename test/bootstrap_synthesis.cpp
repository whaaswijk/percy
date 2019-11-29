#include <percy/percy.hpp>
#include <cassert>

void test_simple()
{
  percy::chain chain;
  percy::spec spec;
  spec.verbosity = 0;

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

void test_simple2()
{
  percy::chain chain;
  percy::spec spec;
  spec.verbosity = 0;
  spec.set_primitive( percy::AIG );

  kitty::dynamic_truth_table f( 6 );
  kitty::create_from_hex_string( f, "0202022200000022" );
  std::cout << kitty::to_hex( f ) << std::endl;

  kitty::dynamic_truth_table a( 6 );
  kitty::dynamic_truth_table b( 6 );
  kitty::create_from_hex_string( a, "0f0f0f0f00000000" );
  kitty::create_from_hex_string( b, "ffffff00ffffff00" );
  spec.add_function( a );
  spec.add_function( b );

  spec[0] = f;

  auto const result = percy::synthesize( spec, chain );
  assert( result == percy::success );

  assert( chain.simulate()[0] == spec[0] );

#if 1
  kitty::dynamic_truth_table x1( 6 );
  kitty::dynamic_truth_table x2( 6 );
  kitty::dynamic_truth_table x3( 6 );
  kitty::dynamic_truth_table x4( 6 );
  kitty::dynamic_truth_table x5( 6 );
  kitty::dynamic_truth_table x6( 6 );
  kitty::create_nth_var( x1, 0u );
  kitty::create_nth_var( x2, 1u );
  kitty::create_nth_var( x3, 2u );
  kitty::create_nth_var( x4, 3u );
  kitty::create_nth_var( x5, 4u );
  kitty::create_nth_var( x6, 5u );

  auto const x7 = a;
  auto const x8 = b;
  auto const x9 =  x1 & ~x2;   // 1.
  auto const x10 = ~x7 &  x8;  // 2.
  auto const x11 =  x9 & ~x10; // 3.
  assert( x11 == spec[0] );
#endif

  assert( chain.get_nr_steps() == 3u );
}

int main()
{
  test_simple();
  test_simple2();
}
