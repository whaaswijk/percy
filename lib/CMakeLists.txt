if (NOT TARGET kitty)
  add_library(kitty INTERFACE) # v0.6
  target_include_directories(kitty INTERFACE ${CMAKE_CURRENT_SOURCE_DIR}/kitty)
endif()
