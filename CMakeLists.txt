cmake_minimum_required (VERSION 2.8)

include(${CMAKE_ROOT}/Modules/ExternalProject.cmake)

project(percy LANGUAGES C CXX)

set(CMAKE_CXX_STANDARD 14)
set(CMAKE_CXX_FLAGS "-Wall -fPIC -DLIN64")

enable_testing()

option(TRAVIS_BUILD "Use Travis build configuration" OFF)
option(PERCY_BUILD_ABC "Build ABC from source for percy" ON)
option(PERCY_TEST "Build tests" OFF)

if( PERCY_BUILD_ABC )
externalproject_add(
    abc
    HG_REPOSITORY "https://bitbucket.org/alanmi/abc"
    PREFIX "abc"
    CONFIGURE_COMMAND ""
    UPDATE_COMMAND ""
    BUILD_COMMAND make ABC_USE_PIC=1 -j4 libabc.so && make
    BUILD_IN_SOURCE 1
    INSTALL_COMMAND ""
)

SET(ABC_INCLUDE_DIR "${PROJECT_BINARY_DIR}/abc/src/abc/src")
SET(ABC_LDIR "${PROJECT_BINARY_DIR}/abc/src/abc") 

add_library(libabc SHARED IMPORTED)
set_target_properties(libabc PROPERTIES IMPORTED_LOCATION ${ABC_LDIR}/libabc.so)
endif()

externalproject_add(
    nauty
    URL "http://pallini.di.uniroma1.it/nauty26r10.tar.gz"
    PREFIX "nauty"
    CONFIGURE_COMMAND "./configure"
    UPDATE_COMMAND ""
    BUILD_COMMAND make -j4
    BUILD_IN_SOURCE 1
    INSTALL_COMMAND ""
)

if (${TRAVIS_BUILD})
    set(CMAKE_CXX_FLAGS "${CMAKE_CXX_FLAGS} -DTRAVIS_BUILD")
endif()

SET(ABC_INCLUDE_DIR "${CMAKE_CURRENT_BINARY_DIR}/abc/src/abc/src")
SET(ABC_LDIR "${CMAKE_CURRENT_BINARY_DIR}/abc/src/abc")

SET(NAUTY_INCLUDE_DIR "${CMAKE_CURRENT_BINARY_DIR}/nauty/src/nauty")
SET(NAUTY_LDIR "${CMAKE_CURRENT_BINARY_DIR}/nauty/src/nauty")

add_library(libnauty STATIC IMPORTED)
set_target_properties(libnauty PROPERTIES IMPORTED_LOCATION ${NAUTY_LDIR}/nautyL1.a)
set_target_properties(libnauty PROPERTIES INTERFACE_INCLUDE_DIRECTORIES ${NAUTY_INCLUDE_DIR})

include_directories(include "kitty/include" ${ABC_INCLUDE_DIR} "glucose" 
    "pat/include" "pat/lib/range-v3/include" "pat/lib/fmt" ${NAUTY_INCLUDE_DIR})

include_directories(${CMAKE_CURRENT_BINARY_DIR})
add_subdirectory(glucose)
#add_subdirectory(nauty)

add_subdirectory(include)

if( PERCY_TEST )
  add_subdirectory(test)
endif()

