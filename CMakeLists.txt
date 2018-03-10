cmake_minimum_required (VERSION 2.8)

include(${CMAKE_ROOT}/Modules/ExternalProject.cmake)

project(percy LANGUAGES C CXX)

set(CMAKE_CXX_STANDARD 14)
set(CMAKE_CXX_FLAGS "-Wall -fPIC -DLIN64")

enable_testing()

option(TRAVIS_BUILD "Use Travis build configuration" OFF)

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

set(ABC_USE_NAMESPACE "abc")
add_subdirectory(abc)
target_compile_definitions(libabc-pic PUBLIC "LIN64")

SET(NAUTY_INCLUDE_DIR "${PROJECT_BINARY_DIR}/nauty/src/nauty")
SET(NAUTY_LDIR "${PROJECT_BINARY_DIR}/nauty/src/nauty") 

add_library(libnauty STATIC IMPORTED)
set_target_properties(libnauty PROPERTIES IMPORTED_LOCATION ${NAUTY_LDIR}/nautyL1.a)

include_directories(include "kitty/include" "glucose" 
    "pat/include" "pat/lib/range-v3/include" "pat/lib/fmt" ${NAUTY_INCLUDE_DIR})

include_directories(${PROJECT_SOURCE_DIR})
add_subdirectory(glucose)
add_subdirectory(bench)
add_subdirectory(test)

