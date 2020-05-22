# -*- mode:cmake -*-
cmake_minimum_required(VERSION 3.13)

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

set(CMAKE_CXX_STANDARD 17)

# Python
find_package(Python3 3.3 REQUIRED COMPONENTS Interpreter Development)
include_directories(${Python3_INCLUDE_DIRS})
message(STATUS "Python3_LIBRARIES = ${Python3_LIBRARIES}")
message(STATUS "Python3_EXECUTABLE = ${Python3_EXECUTABLE}")
message(STATUS "Python3_INCLUDE_DIRS = ${Python3_INCLUDE_DIRS}")
message(STATUS "Python3_RUNTIME_LIBRARY_DIRS = ${Python3_RUNTIME_LIBRARY_DIRS}")

# Directories
set(CMAKE_RUNTIME_OUTPUT_DIRECTORY ${CMAKE_BINARY_DIR}/)
set(CMAKE_BUILD_FILES_DIRECTORY ${dir})
set(CMAKE_BUILD_DIRECTORY ${dir})

# C++ Compilation line
if(NOT NO_TCMALLOC)
  set (TCMALLOC_COMPILE_OPTIONS "-fno-builtin-malloc -fno-builtin-calloc -fno-builtin-realloc -fno-builtin-free")
endif(NOT NO_TCMALLOC)

set(CMAKE_CXX_FLAGS  "${CMAKE_CXX_FLAGS} ${TCMALLOC_COMPILE_OPTIONS} ${MY_CXX_WARNING_FLAGS}")
set(CMAKE_CXX_FLAGS_DEBUG  "${CMAKE_CXX_FLAGS_DEBUG} ${TCMALLOC_COMPILE_OPTIONS} -Wall -O0 -g ${MY_CXX_WARNING_FLAGS}")
set(CMAKE_CXX_FLAGS_RELEASE "${CMAKE_CXX_FLAGS_RELEASE} ${TCMALLOC_COMPILE_OPTIONS} -Wall -O3 -DNDEBUG ${MY_CXX_WARNING_FLAGS}")

set (INCLUDE_DIR "${INSTALL_DIR}/include/surelog/")

include_directories(${INCLUDE_DIR})
include_directories("${INSTALL_DIR}/include/uhdm/")
include_directories("${INSTALL_DIR}/include/uhdm/include/")

set (LIB_DIR "${INSTALL_DIR}/lib/")

if(NOT NO_TCMALLOC)
  set (TCMALLOC_LIBRARY tcmalloc)
endif(NOT NO_TCMALLOC)

set (INSTALL_LIBRARIES_FOR_SURELOG
  -L${LIB_DIR}surelog/ surelog
  antlr4-runtime
  flatbuffers
  uhdm
  -L${LIB_DIR}uhdm/
  capnp kj
  ${Python3_LIBRARIES} dl util m rt pthread ${TCMALLOC_LIBRARY}
)

add_executable(test_hellosureworld ${PROJECT_SOURCE_DIR}/../../src/hellosureworld.cpp)
target_link_libraries(test_hellosureworld ${INSTALL_LIBRARIES_FOR_SURELOG})
target_link_libraries(test_hellosureworld stdc++fs)
