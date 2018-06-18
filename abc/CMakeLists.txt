cmake_minimum_required (VERSION 3.6)

project(libabc LANGUAGES CXX)

include_directories(${PROJECT_SOURCE_DIR})
file(GLOB ABC_SRC *.cpp)

if (STATIC_LIBABC)
    add_library(libabcsat STATIC EXCLUDE_FROM_ALL ${ABC_SRC})
    set_property(TARGET libabcsat PROPERTY OUTPUT_NAME abc)
else()
    add_library(libabcsat SHARED EXCLUDE_FROM_ALL ${ABC_SRC})
    set_property(TARGET libabcsat PROPERTY OUTPUT_NAME abc)
    set_property(TARGET libabcsat PROPERTY POSITION_INDEPENDENT_CODE ON)
endif()
target_include_directories(libabcsat INTERFACE ${PROJECT_SOURCE_DIR})
