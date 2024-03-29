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
set(CMAKE_MSVC_RUNTIME_LIBRARY "MultiThreaded$<$<CONFIG:Debug>:Debug>DLL")

set(CMAKE_CXX_STANDARD 17)
set(CMAKE_CXX_STANDARD_REQUIRED ON)
set(CMAKE_EXPORT_COMPILE_COMMANDS ON)

cmake_path(CONVERT "${INSTALL_DIR}" TO_CMAKE_PATH_LIST INSTALL_DIR)
list(APPEND CMAKE_MODULE_PATH "${INSTALL_DIR}/lib/cmake/")
list(APPEND CMAKE_MODULE_PATH "${INSTALL_DIR}/lib/cmake/UHDM")
list(APPEND CMAKE_MODULE_PATH "${INSTALL_DIR}/lib/cmake/Surelog")
list(APPEND CMAKE_MODULE_PATH "${CMAKE_SOURCE_DIR}/../../cmake/modules")

# Dependencies
find_package(Surelog REQUIRED)

set(CMAKE_THREAD_PREFER_PTHREAD TRUE)
set(THREADS_PREFER_PTHREAD_FLAG TRUE)
find_package(Threads REQUIRED)

if(SURELOG_USE_HOST)
  find_package(ANTLR REQUIRED)
  find_package(UHDM REQUIRED)
  find_package(CapnProto)
  set(UHDM_LIBRARY uhdm::uhdm)
  set(CAPNPROTO_LIBRARY CapnProto::capnp)
  find_package(GTest REQUIRED)
  find_package(nlohmann_json)
  get_target_property(JSON_INCLUDE_DIR nlohmann_json INTERFACE_INCLUDE_DIRECTORIES)
else()
  set(ANTLR_LIBRARY antlr4-runtime$<$<BOOL:${WIN32}>:-static>)
  set(UHDM_LIBRARY uhdm)
  set(UHDM_LIB_DIR "${INSTALL_DIR}/lib/uhdm" "${INSTALL_DIR}/lib64/uhdm")
  set(CAPNPROTO_LIBRARY capnp kj)
endif()

# Python
if (SURELOG_WITH_PYTHON)
  find_package(Python3 3.3 REQUIRED COMPONENTS Interpreter Development)
  message(STATUS "Python3_LIBRARIES = ${Python3_LIBRARIES}")
  message(STATUS "Python3_EXECUTABLE = ${Python3_EXECUTABLE}")
  message(STATUS "Python3_INCLUDE_DIRS = ${Python3_INCLUDE_DIRS}")
  message(STATUS "Python3_RUNTIME_LIBRARY_DIRS = ${Python3_RUNTIME_LIBRARY_DIRS}")
endif()

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
  ${SURELOG_INCLUDE_DIRS}
  ${UHDM_INCLUDE_DIRS}
  ${Python3_INCLUDE_DIRS}
)

target_link_directories(test_hellosureworld
    PRIVATE ${INSTALL_DIR}/lib
    PRIVATE ${SURELOG_LIB_DIR}
    PRIVATE ${UHDM_LIB_DIR}
)

if (SURELOG_WITH_PYTHON)
  target_link_libraries(test_hellosureworld
    surelog::surelog
    ${ANTLR_LIBRARY}
    ${UHDM_LIBRARY}
    ${CAPNPROTO_LIBRARY}
    ${Python3_LIBRARIES}
    $<$<BOOL:${TCMALLOC_LIBRARY}>:tcmalloc>
)
else()
  target_link_libraries(test_hellosureworld
    surelog::surelog
    ${ANTLR_LIBRARY}
    ${UHDM_LIBRARY}
    ${CAPNPROTO_LIBRARY}
    $<$<BOOL:${TCMALLOC_LIBRARY}>:tcmalloc>
)
endif()

if (APPLE)
  target_link_libraries(test_hellosureworld
      dl
      util
      m
      pthread
  )
elseif (UNIX)
  target_link_libraries(test_hellosureworld
      stdc++fs
      dl
      util
      m
      rt
      pthread
  )
endif()

if (WIN32 AND SURELOG_WITH_PYTHON)
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
