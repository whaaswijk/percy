cmake_minimum_required (VERSION 3.6)

include(${CMAKE_ROOT}/Modules/ExternalProject.cmake)

project(percy LANGUAGES CXX)

set(CMAKE_CXX_STANDARD 14)
set(CMAKE_CXX_FLAGS "-Wall -pedantic -fPIC")
if (UNIX)
    set(CMAKE_CXX_FLAGS "${CMAKE_CXX_FLAGS} -DLIN64")
endif()

option(TRAVIS_BUILD "Use Travis build configuration" OFF)
option(PERCY_TEST "Build tests" OFF)
option(PERCY_BENCH "Build benchmarks" OFF)
option(PERCY_BUILD_KITTY "Build kitty for percy" ON)
option(PERCY_BUILD_ABC "Build abc for percy" ON)
option(PERCY_USE_SYRUP "Use glucose-syrup instead of glucose" ON)
option(PERCY_BUILD_CMS "Enables support for CryptoMinisat" OFF)

if (${TRAVIS_BUILD})
    set(CMAKE_CXX_FLAGS "${CMAKE_CXX_FLAGS} -DTRAVIS_BUILD")
endif()

if (PERCY_BUILD_ABC)
  set(ABC_USE_NAMESPACE "abc")
  add_subdirectory(abc)
  if (UNIX)
      target_compile_definitions(libabc-pic PUBLIC "LIN64" ABC_NAMESPACE=abc ABC_NO_USE_READLINE)
  else()
      target_compile_definitions(libabc-pic PUBLIC ABC_NAMESPACE=abc ABC_NO_USE_READLINE)
  endif()
endif()

# Glucose and Glucose-Syrup don't build properly on Windows
if (UNIX)
    if (PERCY_USE_SYRUP)
        set(CMAKE_CXX_FLAGS "${CMAKE_CXX_FLAGS} -DUSE_SYRUP")
        add_subdirectory(syrup)
    else()
        add_subdirectory(glucose)
    endif()
endif()

if (PERCY_BUILD_KITTY)
    add_subdirectory(kitty EXCLUDE_FROM_ALL)
endif()
add_subdirectory(include)

if (PERCY_BUILD_CMS)
    set(CMAKE_CXX_FLAGS "${CMAKE_CXX_FLAGS} -DUSE_CMS")
    add_subdirectory(cryptominisat)
    SET(CMS_INCLUDE_DIR "${PROJECT_BINARY_DIR}/cryptominisat/include") 
    SET(CMS_LDIR "${PROJECT_BINARY_DIR}/cryptominisat/lib") 
    include_directories(${CMS_INCLUDE_DIR})
    link_directories(${CMS_LDIR})
endif()

if (PERCY_BENCH)
    add_subdirectory(bench)
endif()

if (PERCY_TEST)
    enable_testing()
    add_subdirectory(test)
endif()

add_subdirectory(nauty)
