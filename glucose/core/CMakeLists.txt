file(GLOB FILENAMES "Solver.cc")

add_library(glucose ${FILENAMES})
target_include_directories(glucose PUBLIC ${CMAKE_CURRENT_SOURCE_DIR}/../..)
target_include_directories(glucose PUBLIC ${CMAKE_CURRENT_SOURCE_DIR}/..)
