# -*- mode:cmake -*-

project(HELLOSUREWORLD)

set(CMAKE_CXX_STANDARD 11)

cmake_minimum_required(VERSION 3.0)

# Python
find_package(PythonLibs 3.3 REQUIRED)
INCLUDE_DIRECTORIES(${PYTHON_INCLUDE_DIRS})
message(STATUS "PYTHON_LIBRARIES = ${PYTHON_LIBRARIES}")
message(STATUS "PYTHON_EXECUTABLE = ${PYTHON_EXECUTABLE}")
message(STATUS "PYTHON_INCLUDE_DIRS = ${PYTHON_INCLUDE_DIRS}")

# Directories
set(CMAKE_RUNTIME_OUTPUT_DIRECTORY ${CMAKE_BINARY_DIR}/)
set(CMAKE_BUILD_FILES_DIRECTORY ${dir})
set(CMAKE_BUILD_DIRECTORY ${dir})

# C++
set(CMAKE_CXX_FLAGS  "${CMAKE_CXX_FLAGS} -fno-builtin-malloc -fno-builtin-calloc -fno-builtin-realloc -fno-builtin-free ${MY_CXX_WARNING_FLAGS}")
set(CMAKE_CXX_FLAGS_DEBUG  "${CMAKE_CXX_FLAGS_DEBUG} -fno-builtin-malloc -fno-builtin-calloc -fno-builtin-realloc -fno-builtin-free -O0 -g ${MY_CXX_WARNING_FLAGS}")
set(CMAKE_CXX_FLAGS_RELEASE "${CMAKE_CXX_FLAGS_RELEASE} -fno-builtin-malloc -fno-builtin-calloc -fno-builtin-realloc -fno-builtin-free -O3 -DNDEBUG ${MY_CXX_WARNING_FLAGS}")

set (INCLUDE_DIR "${INSTALL_DIR}/include/surelog/")

include_directories(${INCLUDE_DIR})

set (LIB_DIR "${INSTALL_DIR}/lib/surelog/")

set (INSTALL_LIBRARIES_FOR_SURELOG -L${LIB_DIR} surelog antlr4-runtime flatbuffers
  ${PYTHON_LIBRARIES} dl util m rt pthread tcmalloc
)

add_executable(test_hellosureworld ${PROJECT_SOURCE_DIR}/../../src/hellosureworld.cpp)
target_link_libraries(
  test_hellosureworld ${INSTALL_LIBRARIES_FOR_SURELOG} 
)
