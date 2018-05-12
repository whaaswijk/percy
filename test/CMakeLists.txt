if(UNIX)
    set(CMAKE_CXX_FLAGS "${CMAKE_CXX_FLAGS} -g -Wall -Wextra -Wno-unused-function")
else()
    set(CMAKE_CXX_FLAGS "${CMAKE_CXX_FLAGS} -DDISABLE_NAUTY -DDISABLE_GLUCOSE")
endif()

file(GLOB FILENAMES *.cpp)

foreach(FILENAME ${FILENAMES})
    get_filename_component(BASENAME ${FILENAME} NAME_WE)

    set(TARGET_NAME ${BASENAME})

    add_executable(${TARGET_NAME} ${FILENAME})
    target_link_libraries(${TARGET_NAME} percy)
    add_test(${TARGET_NAME} ${TARGET_NAME})
endforeach()

