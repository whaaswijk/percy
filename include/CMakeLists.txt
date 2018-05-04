add_library(percy INTERFACE)
target_include_directories(percy INTERFACE ${PROJECT_SOURCE_DIR}/include)

target_link_libraries(percy INTERFACE kitty libabc libnauty)
if (PERCY_USE_SYRUP)
    target_link_libraries(percy INTERFACE syrup)
else()
    target_link_libraries(percy INTERFACE glucose)
endif()

if (PERCY_BUILD_CMS)
    target_link_libraries(percy INTERFACE cryptominisat5)
endif()
