file(GLOB srcs *.cpp)

add_library(satoko STATIC EXCLUDE_FROM_ALL ${srcs})
set_property(TARGET satoko PROPERTY OUTPUT_NAME satoko)

# Surpress warnings in external library
if (UNIX)
    set(CMAKE_CXX_FLAGS "-w")
endif()

target_include_directories(satoko PUBLIC ${CMAKE_CURRENT_SOURCE_DIR}/..)
target_include_directories(satoko PUBLIC ${CMAKE_CURRENT_SOURCE_DIR})
target_include_directories(satoko PUBLIC ${CMAKE_CURRENT_SOURCE_DIR}/../abc)
