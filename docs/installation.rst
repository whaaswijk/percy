Installation
============

Percy is a header-only library. As such, no build steps are required to start
using it. Simply add ${PERCY_ROOT}/include to your compiler's include path and
you're good to go. However, if you want to run the tests, you'll need to build
some binaries.

The following software is required to build the tests: 
* git (at least version 1.6.5)
* mercurial (at least version 4.x)
* cmake (at least version 3.0.0)
* g++ (at least version 4.9.0) or clang++ (at least version 3.5.0)

Once those requirements are met, run the following commands (or your operating
system's equivalent) to build and run the tests:

    git clone --recurse-submodules https://github.com/whaaswijk/percy.git
    cd percy
    mkdir build
    cd build
    cmake .. -DPERCY_TEST=ON
    make
    make test
