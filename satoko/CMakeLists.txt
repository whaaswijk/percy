cmake_minimum_required (VERSION 3.6)

project(satoko LANGUAGES CXX)

# Surpress warnings in external library
if (UNIX)
    set(CMAKE_CXX_FLAGS "-w")
endif()

file(GLOB srcs *.cpp)

add_library(satoko STATIC EXCLUDE_FROM_ALL ${srcs})
if(WIN32)
    target_compile_definitions(satoko PUBLIC ABC_NAMESPACE=pabc ABC_USE_NO_READLINE NOMINMAX WIN32_NO_DLL)
endif()
set_property(TARGET satoko PROPERTY OUTPUT_NAME satoko)
target_include_directories(satoko PUBLIC ${CMAKE_CURRENT_SOURCE_DIR}/..)
target_include_directories(satoko PUBLIC ${CMAKE_CURRENT_SOURCE_DIR})
target_include_directories(satoko PUBLIC ${CMAKE_CURRENT_SOURCE_DIR}/../abc)
