[![License: MIT](https://img.shields.io/badge/License-MIT-yellow.svg)](https://opensource.org/licenses/MIT)

# percy
<img src="https://cdn.rawgit.com/whaaswijk/percy/master/percy.svg?" width="64" height="64" align="left" style="margin-right: 12pt" />
percy is a header-only exact synthesis library. It offers a collection of
different synthesizers and exact synthesis methods for use in various
applications.

## Quick installation guide

Percy is a header-only library. As such, no build steps are required to start
using it. However, if you want to run the tests, you'll need to build some
binaries.

The following software is required to build the tests: 
* git (at least version 1.6.5)
* mercurial (at least version 4.x)
* cmake (at least version 3.0.0)
* g++ (at least version 4.9.0) or clang++ (at least version 3.5.0)
* boost (at least version 1.56.0)

Once those requirements are met, run the following commands (or your operating
system's equivalent) to build the tests:

    git clone --recurse-submodules https://github.com/whaaswijk/percy.git
    cd percy
    mkdir build
    cd build
    cmake ..
    make

The test will then be available under ${PERCY\_ROOT}/build/test .


