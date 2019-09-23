#include <percy/percy.hpp>

void test_majority_chain()
{
  percy::majority_chain chain;

  /* empty chain */
  chain.reset( 0u, 1u, 0u );
  chain.set_output( 0, 0 );
  assert( kitty::to_hex( chain.simulate()[0u] ) == "0" );

  /* empty chain over two variable */
  chain.reset( 2u, 1u, 0u );
  chain.set_output( 0, 0 );
  assert( kitty::to_hex( chain.simulate()[0u] ) == "0" );

  /* empty chain with first variable as output */
  chain.set_output( 0, 2 );
  assert( kitty::to_hex( chain.simulate()[0u] ) == "a" );

  /* empty chain with second variable as output */
  chain.set_output( 0, 4 );
  assert( kitty::to_hex( chain.simulate()[0u] ) == "c" );

  /* chain with AND */
  chain.reset( 2u, 1u, 1u );
  chain.set_step( 0, 1, 2, 0, 0 ); /* <a b 0> */
  chain.set_output( 0, 6 );
  assert( kitty::to_hex( chain.simulate()[0u] ) == "8" );

  /* chain with OR */
  chain.reset( 2u, 1u, 1u );
  chain.set_step( 0, 1, 2, 0, 3 ); /* <a b ~0> */
  chain.set_output( 0, 6 );
  assert( kitty::to_hex( chain.simulate()[0u] ) == "e" );

  /* chain with MAJ */
  chain.reset( 3u, 1u, 1u );
  chain.set_step( 0, 1, 2, 3, 0 ); /* <a b c> */
  chain.set_output( 0, 8 );
  assert( kitty::to_hex( chain.simulate()[0u] ) == "e8" );
}

void test_majority_expression()
{
  percy::majority_chain chain;
  chain.reset( 3u, 1u, 1u );
  chain.set_step( 0, 1, 2, 3, 0 ); /* <a b c> */
  chain.set_output( 0, 8 );
  assert( chain.to_expression() == "<abc>" );

  chain.reset( 3u, 1u, 1u );
  chain.set_step( 0, 1, 2, 3, 1 ); /* <~a b c> */
  chain.set_output( 0, 8 );
  assert( chain.to_expression() == "<~abc>" );

  chain.reset( 3u, 1u, 1u );
  chain.set_step( 0, 1, 2, 3, 2 ); /* <a ~b c> */
  chain.set_output( 0, 8 );
  assert( chain.to_expression() == "<a~bc>" );

  chain.reset( 3u, 1u, 1u );
  chain.set_step( 0, 1, 2, 3, 3 ); /* <a b ~c> */
  chain.set_output( 0, 8 );
  assert( chain.to_expression() == "<ab~c>" );
}

int main()
{
  test_majority_chain();
  test_majority_expression();
  return 0;
}


