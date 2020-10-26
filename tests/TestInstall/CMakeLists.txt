# -*- mode:cmake -*-
cmake_minimum_required(VERSION 3.15)

# Usage:
# After a make install at the top drectory:
# cd tests/TestInstall;
# rm -rf build;
# mkdir -p build;
# cd build;
# cmake ../ -DINSTALL_DIR=/usr/local;
# make
# ./test_hellosureworld --version

project(HELLOSUREWORLD)

# NOTE: Policy changes has to happen before adding any subprojects
cmake_policy(SET CMP0091 NEW)
set(CMAKE_MSVC_RUNTIME_LIBRARY "MultiThreaded$<$<CONFIG:Debug>:Debug>")

set(CMAKE_CXX_STANDARD 17)
set(CMAKE_CXX_STANDARD_REQUIRED ON)
set(CMAKE_EXPORT_COMPILE_COMMANDS ON)

# Python
find_package(Python3 3.3 REQUIRED COMPONENTS Interpreter Development)
message(STATUS "Python3_LIBRARIES = ${Python3_LIBRARIES}")
message(STATUS "Python3_EXECUTABLE = ${Python3_EXECUTABLE}")
message(STATUS "Python3_INCLUDE_DIRS = ${Python3_INCLUDE_DIRS}")
message(STATUS "Python3_RUNTIME_LIBRARY_DIRS = ${Python3_RUNTIME_LIBRARY_DIRS}")

if(NOT NO_TCMALLOC)
  find_library(TCMALLOC_LIBRARY NAMES tcmalloc)
endif()

# Directories
set(CMAKE_RUNTIME_OUTPUT_DIRECTORY ${CMAKE_BINARY_DIR})

set(CMAKE_CXX_FLAGS  "${CMAKE_CXX_FLAGS} ${TCMALLOC_COMPILE_OPTIONS} ${MY_CXX_WARNING_FLAGS}")
if(MSVC)
  set(CMAKE_CXX_FLAGS_DEBUG  "${CMAKE_CXX_FLAGS_DEBUG} ${TCMALLOC_COMPILE_OPTIONS} /Zc:__cplusplus /W0 /bigobj ${MY_CXX_WARNING_FLAGS}")
  set(CMAKE_CXX_FLAGS_RELEASE "${CMAKE_CXX_FLAGS_RELEASE} ${TCMALLOC_COMPILE_OPTIONS} /Zc:__cplusplus /W0 /bigobj ${MY_CXX_WARNING_FLAGS}")
else()
  # C++ Compilation line
  if($<BOOL:${TCMALLOC_LIBRARY}>)
    set (TCMALLOC_COMPILE_OPTIONS "-fno-builtin-malloc -fno-builtin-calloc -fno-builtin-realloc -fno-builtin-free")
  endif($<BOOL:${TCMALLOC_LIBRARY}>)

  set(CMAKE_CXX_FLAGS_DEBUG  "${CMAKE_CXX_FLAGS_DEBUG} ${TCMALLOC_COMPILE_OPTIONS} -Wall -O0 -g ${MY_CXX_WARNING_FLAGS}")
  set(CMAKE_CXX_FLAGS_RELEASE "${CMAKE_CXX_FLAGS_RELEASE} ${TCMALLOC_COMPILE_OPTIONS} -Wall -O3 -DNDEBUG ${MY_CXX_WARNING_FLAGS}")
endif()

add_executable(test_hellosureworld ${PROJECT_SOURCE_DIR}/../../src/hellosureworld.cpp)
target_include_directories(test_hellosureworld PRIVATE
  ${INSTALL_DIR}/include/surelog
  ${INSTALL_DIR}/include/uhdm
  ${INSTALL_DIR}/include/uhdm/include
  ${Python3_INCLUDE_DIRS}
)
target_link_directories(test_hellosureworld
    PRIVATE ${INSTALL_DIR}/lib/surelog
    PRIVATE ${INSTALL_DIR}/lib/uhdm
)

target_link_libraries(test_hellosureworld
    surelog
    antlr4-runtime$<$<CXX_COMPILER_ID:MSVC>:-static>
    flatbuffers
    uhdm
    capnp
    kj
    ${Python3_LIBRARIES}
    $<$<BOOL:${TCMALLOC_LIBRARY}>:tcmalloc>
)

if (UNIX)
  target_link_libraries(test_hellosureworld
      stdc++fs
      dl
      util
      m
      rt
      pthread
  )
endif()

if (WIN32)
  add_custom_command(
    TARGET test_hellosureworld
    POST_BUILD
    COMMAND ${CMAKE_COMMAND} -E copy_if_different
            ${Python3_RUNTIME_LIBRARY_DIRS}/python${Python3_VERSION_MAJOR}${Python3_VERSION_MINOR}$<$<CONFIG:Debug>:_d>.dll
            $<TARGET_FILE_DIR:test_hellosureworld>)
endif()

add_custom_target(RunInstallTest ALL
    DEPENDS test_hellosureworld
    COMMAND $<TARGET_FILE:test_hellosureworld> --version
    WORKING_DIRECTORY $<TARGET_FILE_DIR:test_hellosureworld>)
