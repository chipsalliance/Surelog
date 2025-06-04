cmake_minimum_required(VERSION 3.15 FATAL_ERROR)
project(Surelog CXX)

set(CMAKE_CXX_STANDARD 17)
set(CMAKE_CXX_STANDARD_REQUIRED ON)
set(CMAKE_EXPORT_COMPILE_COMMANDS ON)

set(UHDM_INCLUDES
  ${PROJECT_SOURCE_DIR}/include
)

set(Surelog_INCLUDES
  ${PROJECT_SOURCE_DIR}/include/surelog
)

set(UHDM_DEFINITIONS
  PLI_DLLISPEC=
  PLI_DLLESPEC=
)

set(Surelog_DEFINITIONS
  ANTLR4CPP_STATIC=1
)

if (CMAKE_BUILD_TYPE STREQUAL Debug)
  set(Surelog_CONFIG_DIRECTORY debug)
else()
  set(Surelog_CONFIG_DIRECTORY release)
endif()

add_library(kj STATIC IMPORTED GLOBAL)
add_library(flatbuffers STATIC IMPORTED GLOBAL)

add_library(capnp STATIC IMPORTED GLOBAL)
target_link_libraries(capnp INTERFACE kj)

add_library(uhdm STATIC IMPORTED GLOBAL)
target_link_libraries(uhdm INTERFACE capnp)

add_library(antlr4 STATIC IMPORTED GLOBAL)

add_library(surelog STATIC IMPORTED GLOBAL)
target_link_libraries(surelog INTERFACE antlr4 flatbuffers uhdm)

if (MSVC)
  set_target_properties(kj PROPERTIES
      IMPORTED_LOCATION "${PROJECT_SOURCE_DIR}/lib/windows-cl-${Surelog_CONFIG_DIRECTORY}/uhdm/kj.lib"
  )
  set_target_properties(capnp PROPERTIES
      IMPORTED_LOCATION "${PROJECT_SOURCE_DIR}/lib/windows-cl-${Surelog_CONFIG_DIRECTORY}/uhdm/capnp.lib"
  )
  set_target_properties(uhdm PROPERTIES
      INTERFACE_COMPILE_DEFINITIONS "${UHDM_DEFINITIONS}"
      INTERFACE_INCLUDE_DIRECTORIES "${UHDM_INCLUDES}"
      IMPORTED_LOCATION "${PROJECT_SOURCE_DIR}/lib/windows-cl-${Surelog_CONFIG_DIRECTORY}/uhdm/uhdm.lib"
  )
  set_target_properties(flatbuffers PROPERTIES
      IMPORTED_LOCATION "${PROJECT_SOURCE_DIR}/lib/windows-cl-${Surelog_CONFIG_DIRECTORY}/surelog/flatbuffers.lib"
  )
  set_target_properties(antlr4 PROPERTIES
      IMPORTED_LOCATION "${PROJECT_SOURCE_DIR}/lib/windows-cl-${Surelog_CONFIG_DIRECTORY}/surelog/antlr4-runtime-static.lib"
  )
  set_target_properties(surelog PROPERTIES
      INTERFACE_COMPILE_DEFINITIONS "${Surelog_DEFINITIONS}"
      INTERFACE_INCLUDE_DIRECTORIES "${Surelog_INCLUDES}"
      IMPORTED_LOCATION "${PROJECT_SOURCE_DIR}/lib/windows-cl-${Surelog_CONFIG_DIRECTORY}/surelog/surelog.lib"
  )
elseif(UNIX)
  set_target_properties(kj PROPERTIES
      IMPORTED_LOCATION "${PROJECT_SOURCE_DIR}/lib/ubuntu-gcc-${Surelog_CONFIG_DIRECTORY}/uhdm/libkj.a"
  )
  set_target_properties(capnp PROPERTIES
      IMPORTED_LOCATION "${PROJECT_SOURCE_DIR}/lib/ubuntu-gcc-${Surelog_CONFIG_DIRECTORY}/uhdm/libcapnp.a"
  )
  set_target_properties(uhdm PROPERTIES
      INTERFACE_COMPILE_DEFINITIONS "${UHDM_DEFINITIONS}"
      INTERFACE_INCLUDE_DIRECTORIES "${UHDM_INCLUDES}"
      IMPORTED_LOCATION "${PROJECT_SOURCE_DIR}/lib/ubuntu-gcc-${Surelog_CONFIG_DIRECTORY}/uhdm/libuhdm.a"
  )
  set_target_properties(flatbuffers PROPERTIES
      IMPORTED_LOCATION "${PROJECT_SOURCE_DIR}/lib/ubuntu-gcc-${Surelog_CONFIG_DIRECTORY}/surelog/libflatbuffers.a"
  )
  set_target_properties(antlr4 PROPERTIES
      IMPORTED_LOCATION "${PROJECT_SOURCE_DIR}/lib/ubuntu-gcc-${Surelog_CONFIG_DIRECTORY}/surelog/libantlr4-runtime.a"
  )
  set_target_properties(surelog PROPERTIES
      INTERFACE_COMPILE_DEFINITIONS "${Surelog_DEFINITIONS}"
      INTERFACE_INCLUDE_DIRECTORIES "${Surelog_INCLUDES}"
      IMPORTED_LOCATION "${PROJECT_SOURCE_DIR}/lib/ubuntu-gcc-${Surelog_CONFIG_DIRECTORY}/surelog/libsurelog.a"
  )
endif()
