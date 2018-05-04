cmake_minimum_required (VERSION 2.8)

include(${CMAKE_ROOT}/Modules/ExternalProject.cmake)

project(percy LANGUAGES CXX)

set(CMAKE_CXX_STANDARD 14)
set(CMAKE_CXX_FLAGS "-Wall -pedantic -fPIC -DLIN64")

option(TRAVIS_BUILD "Use Travis build configuration" OFF)
option(PERCY_TEST "Build tests" OFF)
option(PERCY_BENCH "Build benchmarks" OFF)
option(PERCY_BUILD_KITTY "Build kitty for percy" ON)
option(PERCY_BUILD_ABC "Build abc for percy" ON)
option(PERCY_USE_SYRUP "Use glucose-syrup instead of glucose" ON)

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

if (PERCY_BUILD_ABC)
  set(ABC_USE_NAMESPACE "abc")
  add_subdirectory(abc)
  target_compile_definitions(libabc-pic PUBLIC "LIN64" ABC_NAMESPACE=abc)
endif()

SET(NAUTY_INCLUDE_DIR "${PROJECT_BINARY_DIR}/nauty/src/nauty")
SET(NAUTY_LDIR "${PROJECT_BINARY_DIR}/nauty/src/nauty") 

add_library(libnauty STATIC IMPORTED)
set_target_properties(libnauty PROPERTIES INTERFACE_INCLUDE_DIRECTORIES ${NAUTY_INCLUDE_DIR})
set_target_properties(libnauty PROPERTIES IMPORTED_LOCATION ${NAUTY_LDIR}/nautyL1.a)

if (PERCY_USE_SYRUP)
    set(CMAKE_CXX_FLAGS "${CMAKE_CXX_FLAGS} -DUSE_SYRUP")
    add_subdirectory(syrup)
else()
    add_subdirectory(glucose)
endif()


if (PERCY_BUILD_KITTY)
    add_subdirectory(kitty EXCLUDE_FROM_ALL)
endif()
add_subdirectory(include)

if (PERCY_BENCH)
    add_subdirectory(bench)
endif()

if (PERCY_TEST)
    enable_testing()
    add_subdirectory(test)
endif()
