cmake_minimum_required (VERSION 3.6)

project(libabc LANGUAGES CXX)

file(GLOB ABC_SRC *.cpp)

if (STATIC_LIBABC)
    add_library(libabc STATIC EXCLUDE_FROM_ALL ${ABC_SRC})
    set_property(TARGET libabc PROPERTY OUTPUT_NAME abc)
else()
    add_library(libabc SHARED EXCLUDE_FROM_ALL ${ABC_SRC})
    set_property(TARGET libabc PROPERTY OUTPUT_NAME abc)
    set_property(TARGET libabc PROPERTY POSITION_INDEPENDENT_CODE ON)
endif()

target_link_libraries(libabc percy)
