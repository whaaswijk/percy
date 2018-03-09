set(CMAKE_CXX_FLAGS "${CMAKE_CXX_FLAGS} -g -Wall -Wextra -Wno-unused-function")

file(GLOB FILENAMES *.cpp)

foreach(FILENAME ${FILENAMES})
    get_filename_component(BASENAME ${FILENAME} NAME_WE)

    set(TARGET_NAME ${BASENAME})

    add_executable(${TARGET_NAME} ${FILENAME})
    add_dependencies(${TARGET_NAME} abc)
    target_link_libraries(${TARGET_NAME} libabc glucose pthread libnauty)
    add_test(${TARGET_NAME} ${TARGET_NAME})
endforeach()

