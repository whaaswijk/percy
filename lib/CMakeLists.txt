if (NOT TARGET kitty)
  add_library(kitty INTERFACE) # v0.6
  target_include_directories(kitty INTERFACE ${CMAKE_CURRENT_SOURCE_DIR}/kitty)
endif()

if (NOT TARGET fmt)
  add_library(fmt INTERFACE) # v5.3.0
  target_include_directories(fmt INTERFACE ${CMAKE_CURRENT_SOURCE_DIR}/fmt)
  target_compile_definitions(fmt INTERFACE FMT_HEADER_ONLY)
endif()
