[![License: MIT](https://img.shields.io/badge/License-MIT-yellow.svg)](https://opensource.org/licenses/MIT)
[![Build Status](https://travis-ci.org/whaaswijk/percy.svg?branch=master)](https://travis-ci.org/whaaswijk/percy)
[![Documentation Status](http://percy.readthedocs.io/en/latest/?badge=latest)](http://percy.readthedocs.io/en/latest/?badge=latest)

# percy
<img src="https://cdn.rawgit.com/whaaswijk/percy/master/percy.svg" width="78" height="64" align="left" style="margin-right: 12pt" />
percy is a header-only exact synthesis library. It offers a collection of
different synthesizers and exact synthesis methods for use in applications such
as circuit resynthesis and design exploration.

## Quick install guide

Percy is a header-only library. As such, no build steps are required to start
using it. Simply add ${PERCY_ROOT}/include to your compiler's include path and
you're good to go. However, if you want to run the tests, you'll need to build
some binaries.

The following software is required to build the tests: 
* git (at least version 1.6.5)
* mercurial (at least version 4.x)
* cmake (at least version 3.0.0)
* g++ (at least version 4.9.0) or clang++ (at least version 3.5.0)
* libz

Once those requirements are met, run the following commands (or your operating
system's equivalent) to build and run the tests:

    git clone --recurse-submodules https://github.com/whaaswijk/percy.git
    cd percy
    mkdir build
    cd build
    cmake .. -DPERCY_TEST=ON
    make
    make test

## EPFL logic sythesis libraries

percy is part of the [EPFL logic synthesis](https://lsi.epfl.ch/page-138455-en.html) libraries.  The other libraries and several examples on how to use and integrate the libraries can be found in the [logic synthesis tool showcase](https://github.com/lsils/lstools-showcase).
