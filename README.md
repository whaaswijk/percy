[![Build Status](https://travis-ci.org/whaaswijk/percy.svg?branch=master)](https://travis-ci.org/whaaswijk/percy)
[![Documentation Status](https://readthedocs.org/projects/percy/badge/?version=latest)](http://percy.readthedocs.io/en/latest)
[![License: MIT](https://img.shields.io/badge/License-MIT-yellow.svg)](https://opensource.org/licenses/MIT)

# percy
<img src="https://cdn.rawgit.com/whaaswijk/percy/master/percy.svg" width="78" height="64" align="left" style="margin-right: 12pt" />
percy is a header-only exact synthesis library. It offers a collection of
different synthesizers and exact synthesis methods for use in applications such
as circuit resynthesis and design exploration.

[Read the documentation here.](http://percy.readthedocs.io/en/latest/?badge=latest)

+## Example

The following code snippet synthesizes a circuit implementation of a full adder.

```c++
#include <percy/percy.hpp>

spec s;
s.set_nr_outputs( 2 );

chain c;

kitty::dynamic_truth_table x{3}, y{3}, z{3};
kitty::create_nth_var( x, 0 );
kitty::create_nth_var( y, 1 );
kitty::create_nth_var( z, 2 );

auto const sum = x ^ y ^ z;
auto const carry = kitty::ternary_majority( x, y, z );

spec[0] = sum;
spec[1] = carry;

auto const result == synthesize( s, c );
assert( result == success );
```

## EPFL logic sythesis libraries

percy is part of the [EPFL logic synthesis](https://lsi.epfl.ch/page-138455-en.html) libraries.  The other libraries and several examples on how to use and integrate the libraries can be found in the [logic synthesis tool showcase](https://github.com/lsils/lstools-showcase).
