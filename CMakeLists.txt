cmake_minimum_required (VERSION 2.8)

include(${CMAKE_ROOT}/Modules/ExternalProject.cmake)

project(percy LANGUAGES C CXX)

set(CMAKE_CXX_STANDARD 14)
set(CMAKE_CXX_FLAGS "-Wall -fPIC -DLIN64")

option(TRAVIS_BUILD "Use alternative nauty include path" OFF)

enable_testing()

externalproject_add(
	abc
	HG_REPOSITORY "https://bitbucket.org/alanmi/abc"
    PREFIX "abc"
	CONFIGURE_COMMAND ""
	UPDATE_COMMAND ""
	BUILD_COMMAND make ABC_USE_PIC=1 -j8 libabc.so && make
	BUILD_IN_SOURCE 1
	INSTALL_COMMAND ""
)

if (${TRAVIS_BUILD})
    set(CMAKE_CXX_FLAGS "${CMAKE_CXX_FLAGS} -DTRAVIS_BUILD")
endif()

SET(ABC_INCLUDE_DIR "${PROJECT_BINARY_DIR}/abc/src/abc/src")
SET(ABC_LDIR "${PROJECT_BINARY_DIR}/abc/src/abc") 

add_library(libabc SHARED IMPORTED)
set_target_properties(libabc PROPERTIES IMPORTED_LOCATION ${ABC_LDIR}/libabc.so)

include_directories(include "kitty/include" ${ABC_INCLUDE_DIR} "glucose" 
    "pat/include" "pat/lib/range-v3/include" "pat/lib/fmt")

include_directories(${PROJECT_SOURCE_DIR})
add_subdirectory(glucose)
add_subdirectory(test)

