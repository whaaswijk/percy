# Surpress warnings from this external library
if (UNIX)
    set(CMAKE_CXX_FLAGS "-w")
endif()

add_subdirectory(core)
