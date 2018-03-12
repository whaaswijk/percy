add_library(percy INTERFACE)
target_include_directories(percy INTERFACE ${PROJECT_SOURCE_DIR}/include)
target_link_libraries(percy INTERFACE kitty libabc libnauty glucose)
