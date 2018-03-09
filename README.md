[![License: MIT](https://img.shields.io/badge/License-MIT-yellow.svg)](https://opensource.org/licenses/MIT)
[![Build Status](https://travis-ci.org/whaaswijk/percy.svg?branch=master)](https://travis-ci.org/whaaswijk/percy)

# percy
<img src="https://cdn.rawgit.com/whaaswijk/percy/master/percy2.svg" width="78" height="64" align="left" style="margin-right: 12pt" />
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
* boost (at least version 1.56.0)
* libnauty2 (at least version 2.6)

Once those requirements are met, run the following commands (or your operating
system's equivalent) to build the tests:

    git clone --recurse-submodules https://github.com/whaaswijk/percy.git
    cd percy
    mkdir build
    cd build
    cmake ..
    make

The tests will then be available under ${PERCY\_ROOT}/build/test .


