# -*- mode:cmake -*-
cmake_minimum_required (VERSION 2.8)
# 2.8 needed because of ExternalProject

add_subdirectory(third_party/flatbuffers)
add_subdirectory(third_party/antlr4/runtime/Cpp)

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

# Python
find_package(PythonLibs 3.3 REQUIRED)
INCLUDE_DIRECTORIES(${PYTHON_INCLUDE_DIRS})
INCLUDE_DIRECTORIES("${PROJECT_SOURCE_DIR}/third_party/antlr4/runtime/Cpp/runtime/src/")
INCLUDE_DIRECTORIES("${PROJECT_SOURCE_DIR}/third_party/flatbuffers/include/")
message(STATUS "PYTHON_LIBRARIES = ${PYTHON_LIBRARIES}")
message(STATUS "PYTHON_EXECUTABLE = ${PYTHON_EXECUTABLE}")
message(STATUS "PYTHON_INCLUDE_DIRS = ${PYTHON_INCLUDE_DIRS}")

# C++
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

# Flatbuffer

set(flatbuffer-GENERATED_SRC
  ${PROJECT_SOURCE_DIR}/src/Cache/header_generated.h
  ${PROJECT_SOURCE_DIR}/src/Cache/parser_generated.h
  ${PROJECT_SOURCE_DIR}/src/Cache/preproc_generated.h
  ${PROJECT_SOURCE_DIR}/src/Cache/python_api_generated.h
  ${PROJECT_SOURCE_DIR}/src/Cache/ParseCache.cpp
 )

foreach( header_file ${flatbuffer-GENERATED_SRC} )
      set_source_files_properties(
          ${header_file}
          PROPERTIES
          GENERATED TRUE
          )
endforeach( header_file ${flatbuffer-GENERATED_SRC} )
add_custom_target(GenerateSerializer DEPENDS ${flatbuffer-GENERATED_SRC})
add_custom_command(
   OUTPUT ${flatbuffer-GENERATED_SRC}
   COMMAND
   flatc --cpp --binary -o ../src/Cache/ ../src/Cache/header.fbs ../src/Cache/parser.fbs ../src/Cache/preproc.fbs ../src/Cache/python_api.fbs
   WORKING_DIRECTORY "${CMAKE_BINARY_DIR}"
   DEPENDS ${PROJECT_SOURCE_DIR}/src/Cache/parser.fbs ${PROJECT_SOURCE_DIR}/src/Cache/header.fbs ${FLATBUFFERS_FLATC_EXECUTABLE}
   )

# Java
find_package(Java)
find_package(Java COMPONENTS Runtime)
set(ANTLR_JAR_LOCATION ${PROJECT_SOURCE_DIR}/third_party/antlr4/antlr4-4.7.2-complete.jar)
#

enable_testing()
#add_test(NAME GenerateFromGrammar COMMAND ${Java_JAVA_EXECUTABLE}  org.antlr.v4.Tool -Dlanguage=Cpp *.g4)

set(antlr4-sverilog-grammar-GENERATED_SRC
  ${PROJECT_SOURCE_DIR}/src/parser/SV3_1aLexer.cpp                 
  ${PROJECT_SOURCE_DIR}/src/parser/SV3_1aParser.cpp
  ${PROJECT_SOURCE_DIR}/src/parser/SV3_1aSplitterLexer.cpp
  ${PROJECT_SOURCE_DIR}/src/parser/SV3_1aPpLexer.cpp               
  ${PROJECT_SOURCE_DIR}/src/parser/SV3_1aSplitterParser.cpp
  ${PROJECT_SOURCE_DIR}/src/parser/SV3_1aPpParser.cpp
  ${PROJECT_SOURCE_DIR}/src/SourceCompile/VObjectTypes.cpp
 )

foreach( src_file ${antlr4-sverilog-grammar-GENERATED_SRC} )
      set_source_files_properties(
          ${src_file}
          PROPERTIES
          GENERATED TRUE
          )
endforeach( src_file ${antlr4-sverilog-grammar-GENERATED_SRC} )

add_custom_target(GenerateParser DEPENDS ${antlr4-sverilog-grammar-GENERATED_SRC})
add_custom_command(OUTPUT ${antlr4-sverilog-grammar-GENERATED_SRC}
   COMMAND 
   ${CMAKE_COMMAND} -E make_directory ${PROJECT_SOURCE_DIR}/src/parser/
   COMMAND
   "${Java_JAVA_EXECUTABLE}" -jar ${ANTLR_JAR_LOCATION} -Werror -Dlanguage=Cpp -listener -visitor -o ${PROJECT_SOURCE_DIR}/parser/  ${PROJECT_SOURCE_DIR}/grammar/SV3_1aPpLexer.g4 ${PROJECT_SOURCE_DIR}/grammar/SV3_1aSplitterLexer.g4 ${PROJECT_SOURCE_DIR}/grammar/SV3_1aPpParser.g4 ${PROJECT_SOURCE_DIR}/grammar/SV3_1aSplitterParser.g4
   WORKING_DIRECTORY "${CMAKE_BINARY_DIR}"
   DEPENDS ${PROJECT_SOURCE_DIR}/grammar/SV3_1aPpLexer.g4 ${PROJECT_SOURCE_DIR}/grammar/SV3_1aSplitterLexer.g4 ${PROJECT_SOURCE_DIR}/grammar/SV3_1aPpParser.g4 ${PROJECT_SOURCE_DIR}/grammar/SV3_1aSplitterParser.g4
   COMMAND
   SourceCompile/generate_parser_listener.tcl ;
   API/generate_python_listener_api.tcl ;
   API/embed_python_api.tcl ;
   swig -c++ -python  -o API/slapi_wrap.cxx API/slapi.i ;
   WORKING_DIRECTORY "${PROJECT_SOURCE_DIR}/src/"
   DEPENDS ${PROJECT_SOURCE_DIR}/grammar/SV3_1aPpLexer.g4 ${PROJECT_SOURCE_DIR}/grammar/SV3_1aSplitterLexer.g4 ${PROJECT_SOURCE_DIR}/grammar/SV3_1aPpParser.g4 ${PROJECT_SOURCE_DIR}/grammar/SV3_1aSplitterParser.g4
   )

set(CMAKE_BUILD_FILES_DIRECTORY ${dir})
set(CMAKE_BUILD_DIRECTORY ${dir})

set(CMAKE_RUNTIME_OUTPUT_DIRECTORY ${CMAKE_BINARY_DIR}/../src/dist/${CMAKE_BUILD_TYPE}/GNU-Linux/ )

include_directories(
  ${PROJECT_SOURCE_DIR}/src/API
  ${PROJECT_SOURCE_DIR}/src/Design
  ${PROJECT_SOURCE_DIR}/src/Library
  ${PROJECT_SOURCE_DIR}/src/parser
  ${PROJECT_SOURCE_DIR}/src/SourceCompile
  ${PROJECT_SOURCE_DIR}/src/DesignCompile
  ${PROJECT_SOURCE_DIR}/src/Testbench
  ${PROJECT_SOURCE_DIR}/src/CommandLine
  ${PROJECT_SOURCE_DIR}/src/Common
  ${PROJECT_SOURCE_DIR}/src/ErrorReporting
  ${PROJECT_SOURCE_DIR}/src/Utils
  ${PROJECT_SOURCE_DIR}/src/Cache
  ${PROJECT_SOURCE_DIR}/src/Config
  ${PROJECT_SOURCE_DIR}/src/Expression
  ${PROJECT_SOURCE_DIR}/src/Package   
)

file(GLOB surelog_SRC
  ${PROJECT_SOURCE_DIR}/src/*.cpp
  ${PROJECT_SOURCE_DIR}/src/API/*.cpp
  ${PROJECT_SOURCE_DIR}/src/Design/*.cpp
  ${PROJECT_SOURCE_DIR}/src/Library/*.cpp
  ${PROJECT_SOURCE_DIR}/src/parser/*.cpp
  ${PROJECT_SOURCE_DIR}/src/SourceCompile/*.cpp
  ${PROJECT_SOURCE_DIR}/src/DesignCompile/*.cpp
  ${PROJECT_SOURCE_DIR}/src/Testbench/*.cpp
  ${PROJECT_SOURCE_DIR}/src/CommandLine/*.cpp
  ${PROJECT_SOURCE_DIR}/src/Common/*.cpp
  ${PROJECT_SOURCE_DIR}/src/ErrorReporting/*.cpp
  ${PROJECT_SOURCE_DIR}/src/Utils/*.cpp
  ${PROJECT_SOURCE_DIR}/src/Cache/*.cpp
  ${PROJECT_SOURCE_DIR}/src/Config/*.cpp
  ${PROJECT_SOURCE_DIR}/src/Expression/*.cpp
  ${PROJECT_SOURCE_DIR}/src/Package/*.cpp
  )

add_executable(surelog ${surelog_SRC})

add_dependencies(surelog flatc)
add_dependencies(surelog antlr4_static)

add_dependencies(surelog GenerateParser)
add_dependencies(surelog GenerateSerializer)

target_link_libraries(
  surelog ${PYTHON_LIBRARIES}
  )

#target_link_libraries(
#  surelog  ${ANTLR_LIB}
#)

target_link_libraries(
  surelog -L${PROJECT_SOURCE_DIR}/dist/ libantlr4-runtime.a dl util m rt pthread 
)
