# -*- mode:cmake -*-
cmake_minimum_required (VERSION 2.8)
# 2.8 needed because of ExternalProject

# Detect build type, fallback to release and throw a warning if use didn't specify any
if(NOT CMAKE_BUILD_TYPE)
  message(WARNING "Build type not set, falling back to Release mode.
 To specify build type use:
 -DCMAKE_BUILD_TYPE=<mode> where <mode> is Debug or Release.")
  set(CMAKE_BUILD_TYPE "Release" CACHE STRING
       "Choose the type of build, options are: Debug Release."
       FORCE)
endif(NOT CMAKE_BUILD_TYPE)

if(NOT WITH_TEST)
  message(STATUS "Building without test. To enable test build use: -DWITH_TEST=True")
  set(WITH_TEST False CACHE STRING
    "Chose to build with or without test executable"
    FORCE)
endif(NOT WITH_TEST)

option(WITH_LIBCXX "Building with clang++ and libc++(in Linux). To enable with: -DWITH_LIBCXX=On" On)

project(SURELOG)

#file(STRINGS "VERSION" SURELOG_VERSION)

if (WITH_TEST)

endif(WITH_TEST)

set(CMAKE_CXX_STANDARD 11)

cmake_minimum_required(VERSION 3.0)
find_package(PythonLibs 3.3 REQUIRED)
INCLUDE_DIRECTORIES(${PYTHON_INCLUDE_DIRS})
INCLUDE_DIRECTORIES("../antlr4/antlr4-4.7.2/runtime/Cpp/runtime/src/")
INCLUDE_DIRECTORIES("../flatbuffers/include/")
message(STATUS "PYTHON_LIBRARIES = ${PYTHON_LIBRARIES}")
message(STATUS "PYTHON_EXECUTABLE = ${PYTHON_EXECUTABLE}")
message(STATUS "PYTHON_INCLUDE_DIRS = ${PYTHON_INCLUDE_DIRS}")
set(CMAKE_CXX_FLAGS                  "${CMAKE_CXX_FLAGS} ${MY_CXX_WARNING_FLAGS}")
set(CMAKE_CXX_FLAGS_DEBUG          "${CMAKE_CXX_FLAGS_DEBUG} -O0 -g ${MY_CXX_WARNING_FLAGS}")
set(CMAKE_CXX_FLAGS_RELEASE        "${CMAKE_CXX_FLAGS_RELEASE} -O3 -DNDEBUG ${MY_CXX_WARNING_FLGAS}")

# Compiler-specific C++11 activation.
if ("${CMAKE_CXX_COMPILER_ID}" MATCHES "GNU" OR "${CMAKE_CXX_COMPILER_ID}" MATCHES "Intel")
    execute_process(
        COMMAND ${CMAKE_CXX_COMPILER} -dumpversion OUTPUT_VARIABLE GCC_VERSION)
    # Just g++-5.0 and greater contain <codecvt> header. (test in ubuntu)
    if (NOT (GCC_VERSION VERSION_GREATER 5.0 OR GCC_VERSION VERSION_EQUAL 5.0))
        message(FATAL_ERROR "${PROJECT_NAME} requires g++ 5.0 or greater.")
    endif ()
elseif ("${CMAKE_CXX_COMPILER_ID}" MATCHES "Clang" AND APPLE)
    set(CMAKE_CXX_FLAGS "${CMAKE_CXX_FLAGS} -stdlib=libc++")
elseif ("${CMAKE_CXX_COMPILER_ID}" MATCHES "Clang" AND CMAKE_SYSTEM_NAME MATCHES "Linux")
    execute_process(
        COMMAND ${CMAKE_CXX_COMPILER} -dumpversion OUTPUT_VARIABLE CLANG_VERSION)
    if (NOT (CLANG_VERSION VERSION_GREATER 4.2.1 OR CLANG_VERSION VERSION_EQUAL 4.2.1))
        message(FATAL_ERROR "${PROJECT_NAME} requires clang 4.2.1 or greater.")
    endif ()
    # You can use libc++ to compile this project when g++ is NOT greater than or equal to 5.0.
    if (WITH_LIBCXX)
        set(CMAKE_CXX_FLAGS "${CMAKE_CXX_FLAGS} -stdlib=libc++")
    endif()
elseif ( MSVC_VERSION GREATER 1800 OR MSVC_VERSION EQUAL 1800 )
  # Visual Studio 2012+ supports c++11 features 
else ()
    message(FATAL_ERROR "Your C++ compiler does not support C++11.")
endif ()

#if (WITH_DEMO)
# add_subdirectory(demo)
#endif(WITH_DEMO)


#set(dir ${CMAKE_CURRENT_SOURCE_DIR}/../Compile/)
#set(EXECUTABLE_OUTPUT_PATH ${dir} CACHE PATH "Build directory" FORCE)
#set(LIBRARY_OUTPUT_PATH ${dir} CACHE PATH "Build directory" FORCE)
#set(CMAKE_RUNTIME_OUTPUT_DIRECTORY ${dir})
#set(CMAKE_BUILD_FILES_DIRECTORY ${dir})
#set(CMAKE_BUILD_DIRECTORY ${dir})
#set(CMAKE_BINARY_DIR  ${dir})

set(CMAKE_BUILD_FILES_DIRECTORY ${dir})
set(CMAKE_BUILD_DIRECTORY ${dir})

include_directories(
  ${PROJECT_SOURCE_DIR}/API
  ${PROJECT_SOURCE_DIR}/Design
  ${PROJECT_SOURCE_DIR}/Library
  ${PROJECT_SOURCE_DIR}/parser
  ${PROJECT_SOURCE_DIR}/SourceCompile
  ${PROJECT_SOURCE_DIR}/DesignCompile
  ${PROJECT_SOURCE_DIR}/Testbench
  ${PROJECT_SOURCE_DIR}/CommandLine
  ${PROJECT_SOURCE_DIR}/Common
  ${PROJECT_SOURCE_DIR}/ErrorReporting
  ${PROJECT_SOURCE_DIR}/Utils
  ${PROJECT_SOURCE_DIR}/Cache
  ${PROJECT_SOURCE_DIR}/Config
  ${PROJECT_SOURCE_DIR}/Expression
  ${PROJECT_SOURCE_DIR}/Package   
)


file(GLOB surelog_SRC
  ${PROJECT_SOURCE_DIR}/*.cpp
  ${PROJECT_SOURCE_DIR}/API/*.cpp
  ${PROJECT_SOURCE_DIR}/Design/*.cpp
  ${PROJECT_SOURCE_DIR}/Library/*.cpp
  ${PROJECT_SOURCE_DIR}/parser/*.cpp
  ${PROJECT_SOURCE_DIR}/SourceCompile/*.cpp
  ${PROJECT_SOURCE_DIR}/DesignCompile/*.cpp
  ${PROJECT_SOURCE_DIR}/Testbench/*.cpp
  ${PROJECT_SOURCE_DIR}/CommandLine/*.cpp
  ${PROJECT_SOURCE_DIR}/Common/*.cpp
  ${PROJECT_SOURCE_DIR}/ErrorReporting/*.cpp
  ${PROJECT_SOURCE_DIR}/Utils/*.cpp
  ${PROJECT_SOURCE_DIR}/Cache/*.cpp
  ${PROJECT_SOURCE_DIR}/Config/*.cpp
  ${PROJECT_SOURCE_DIR}/Expression/*.cpp
  ${PROJECT_SOURCE_DIR}/Package/*.cpp
  )

add_executable(surelog ${surelog_SRC})

target_link_libraries(
  surelog ${PYTHON_LIBRARIES}
  )

target_link_libraries(
  surelog  ${ANTLR_LIB}
)

target_link_libraries(
  surelog -L../../antlr4/antlr4-4.7.2/runtime/Cpp/dist/ libantlr4-runtime.a dl util m rt pthread 
)
