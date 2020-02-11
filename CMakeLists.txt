# -*- mode:cmake -*-
cmake_minimum_required(VERSION 3.0)

add_subdirectory(third_party/flatbuffers EXCLUDE_FROM_ALL)
add_subdirectory(third_party/antlr4/runtime/Cpp EXCLUDE_FROM_ALL)
add_subdirectory(third_party/UHDM)

find_package(SWIG REQUIRED)

# Detect build type, fallback to release and throw a warning if use didn't
# specify any
if(NOT CMAKE_BUILD_TYPE)
  message(WARNING "Build type not set, falling back to Release mode.
 To specify build type use:
 -DCMAKE_BUILD_TYPE=<mode> where <mode> is Debug or Release.")
  set(CMAKE_BUILD_TYPE
      "Release"
      CACHE STRING "Choose the type of build, options are: Debug Release."
            FORCE)
endif(NOT CMAKE_BUILD_TYPE)

if(NOT NO_TCMALLOC)
  message(
    WARNING "USING TCMALLOC, IF YOU HAVE RUNTIME ISSUES, DISABLE -DNO_TCMALLOC")
endif(NOT NO_TCMALLOC)

option(
  WITH_LIBCXX
  "Building with clang++ and libc++(in Linux). To enable with: -DWITH_LIBCXX=On"
  On)

project(SURELOG)

set(CMAKE_CXX_STANDARD 11)

# Python
find_package(PythonLibs 3.3 REQUIRED)
include_directories(${PYTHON_INCLUDE_DIRS})
message(STATUS "PYTHON_LIBRARIES = ${PYTHON_LIBRARIES}")
message(STATUS "PYTHON_EXECUTABLE = ${PYTHON_EXECUTABLE}")
message(STATUS "PYTHON_INCLUDE_DIRS = ${PYTHON_INCLUDE_DIRS}")

# Includes
include_directories(
  "${PROJECT_SOURCE_DIR}/third_party/antlr4/runtime/Cpp/runtime/src/")
include_directories("${PROJECT_SOURCE_DIR}/third_party/flatbuffers/include/")

include_directories("${PROJECT_SOURCE_DIR}/third_party/UHDM/include/")
include_directories("${PROJECT_SOURCE_DIR}/third_party/UHDM/")
include_directories("${PROJECT_SOURCE_DIR}/third_party/UHDM/headers/")
include_directories("${PROJECT_SOURCE_DIR}/third_party/UHDM/src/")
include_directories(
  "${PROJECT_SOURCE_DIR}/third_party/UHDM/third_party/capnproto/c++/src/")
include_directories(
  "${PROJECT_SOURCE_DIR}/third_party/UHDM/third_party/UHDM/src/")

# Directories
set(CMAKE_RUNTIME_OUTPUT_DIRECTORY
    ${CMAKE_BINARY_DIR}/dist/${CMAKE_BUILD_TYPE}/)
set(CMAKE_BUILD_FILES_DIRECTORY ${dir})
set(CMAKE_BUILD_DIRECTORY ${dir})

# C++ Compilation line
if(NOT NO_TCMALLOC)
  set(TCMALLOC_COMPILE_OPTIONS
      "-fno-builtin-malloc -fno-builtin-calloc -fno-builtin-realloc -fno-builtin-free"
  )
endif(NOT NO_TCMALLOC)

set(CMAKE_CXX_FLAGS
    "${CMAKE_CXX_FLAGS} ${TCMALLOC_COMPILE_OPTIONS} ${MY_CXX_WARNING_FLAGS}")
set(CMAKE_CXX_FLAGS_DEBUG
    "${CMAKE_CXX_FLAGS_DEBUG} ${TCMALLOC_COMPILE_OPTIONS} -Wall -O0 -g ${MY_CXX_WARNING_FLAGS}"
)
set(CMAKE_CXX_FLAGS_RELEASE
    "${CMAKE_CXX_FLAGS_RELEASE} ${TCMALLOC_COMPILE_OPTIONS} -Wall -O3 -DNDEBUG ${MY_CXX_WARNING_FLAGS}"
)

# Flatbuffer
set(flatbuffer-GENERATED_SRC
    ${PROJECT_SOURCE_DIR}/src/Cache/header_generated.h
    ${PROJECT_SOURCE_DIR}/src/Cache/parser_generated.h
    ${PROJECT_SOURCE_DIR}/src/Cache/preproc_generated.h
    ${PROJECT_SOURCE_DIR}/src/Cache/python_api_generated.h)

foreach(header_file ${flatbuffer-GENERATED_SRC})
  set_source_files_properties(${header_file} PROPERTIES GENERATED TRUE)
endforeach(header_file ${flatbuffer-GENERATED_SRC})
add_custom_target(GenerateSerializer DEPENDS ${flatbuffer-GENERATED_SRC})
add_custom_command(
  OUTPUT ${flatbuffer-GENERATED_SRC}
  COMMAND
    flatc --cpp --binary -o ${PROJECT_SOURCE_DIR}/src/Cache/
    ${PROJECT_SOURCE_DIR}/src/Cache/header.fbs
    ${PROJECT_SOURCE_DIR}/src/Cache/parser.fbs
    ${PROJECT_SOURCE_DIR}/src/Cache/preproc.fbs
    ${PROJECT_SOURCE_DIR}/src/Cache/python_api.fbs
  WORKING_DIRECTORY "${CMAKE_BINARY_DIR}"
  DEPENDS ${PROJECT_SOURCE_DIR}/src/Cache/parser.fbs
          ${PROJECT_SOURCE_DIR}/src/Cache/header.fbs
          ${PROJECT_SOURCE_DIR}/src/Cache/preproc.fbs
          ${FLATBUFFERS_FLATC_EXECUTABLE})

# Java
find_package(Java)
find_package(Java COMPONENTS Runtime)
set(ANTLR_JAR_LOCATION
    ${PROJECT_SOURCE_DIR}/third_party/antlr4/antlr4-4.7.2-complete.jar)

add_custom_target(
  GenerateParser DEPENDS ${PROJECT_SOURCE_DIR}/src/parser/dummy1
                         ${PROJECT_SOURCE_DIR}/src/SourceCompile/dummy2)

add_custom_command(
  OUTPUT ${PROJECT_SOURCE_DIR}/src/parser/dummy1
  WORKING_DIRECTORY "${PROJECT_SOURCE_DIR}/grammar/"
  COMMAND echo "       Parser Generation..."
  COMMAND ${CMAKE_COMMAND} -E make_directory ${PROJECT_SOURCE_DIR}/src/parser/
  COMMAND
    java -jar ${ANTLR_JAR_LOCATION} -Werror -Dlanguage=Cpp -o
    ${PROJECT_SOURCE_DIR}/src/parser/ SV3_1aPpLexer.g4 SV3_1aLexer.g4
    SV3_1aSplitterLexer.g4 SV3_1aPpParser.g4 SV3_1aParser.g4
    SV3_1aSplitterParser.g4
  DEPENDS ${PROJECT_SOURCE_DIR}/grammar/SV3_1aPpLexer.g4
          ${PROJECT_SOURCE_DIR}/grammar/SV3_1aLexer.g4
          ${PROJECT_SOURCE_DIR}/grammar/SV3_1aSplitterLexer.g4
          ${PROJECT_SOURCE_DIR}/grammar/SV3_1aPpParser.g4
          ${PROJECT_SOURCE_DIR}/grammar/SV3_1aParser.g4
          ${PROJECT_SOURCE_DIR}/grammar/SV3_1aSplitterParser.g4
  COMMAND touch ${PROJECT_SOURCE_DIR}/src/parser/dummy1
  COMMAND echo "       Parser Generated.")

add_custom_command(
  OUTPUT ${PROJECT_SOURCE_DIR}/src/SourceCompile/dummy2
  WORKING_DIRECTORY "${PROJECT_SOURCE_DIR}/src/"
  COMMAND echo "       Serializer, Parser Listener, code generation..."
  COMMAND SourceCompile/generate_parser_listener.tcl ;
  COMMAND API/generate_python_listener_api.tcl ;
  COMMAND echo "       Python API Generation..."
  COMMAND ${SWIG_EXECUTABLE} -c++ -python -o API/slapi_wrap.cxx API/slapi.i ;
  COMMAND API/embed_python_api.tcl
  COMMAND touch ${PROJECT_SOURCE_DIR}/src/SourceCompile/dummy2
  COMMAND echo "       Code Generation completed"
  DEPENDS ${PROJECT_SOURCE_DIR}/grammar/SV3_1aPpLexer.g4
          ${PROJECT_SOURCE_DIR}/grammar/SV3_1aLexer.g4
          ${PROJECT_SOURCE_DIR}/grammar/SV3_1aSplitterLexer.g4
          ${PROJECT_SOURCE_DIR}/grammar/SV3_1aPpParser.g4
          ${PROJECT_SOURCE_DIR}/grammar/SV3_1aParser.g4
          ${PROJECT_SOURCE_DIR}/grammar/SV3_1aSplitterParser.g4
          ${PROJECT_SOURCE_DIR}/src/API/slapi.i
          ${PROJECT_SOURCE_DIR}/src/parser/dummy1)

include_directories(${PROJECT_SOURCE_DIR}/src)

file(
  GLOB
  surelog_SRC
  ${PROJECT_SOURCE_DIR}/src/parser/SV3_1aLexer.cpp
  ${PROJECT_SOURCE_DIR}/src/parser/SV3_1aParserBaseListener.cpp
  ${PROJECT_SOURCE_DIR}/src/parser/SV3_1aParser.cpp
  ${PROJECT_SOURCE_DIR}/src/parser/SV3_1aParserListener.cpp
  ${PROJECT_SOURCE_DIR}/src/parser/SV3_1aPpLexer.cpp
  ${PROJECT_SOURCE_DIR}/src/parser/SV3_1aPpParserBaseListener.cpp
  ${PROJECT_SOURCE_DIR}/src/parser/SV3_1aPpParser.cpp
  ${PROJECT_SOURCE_DIR}/src/parser/SV3_1aPpParserListener.cpp
  ${PROJECT_SOURCE_DIR}/src/parser/SV3_1aSplitterLexer.cpp
  ${PROJECT_SOURCE_DIR}/src/parser/SV3_1aSplitterParserBaseListener.cpp
  ${PROJECT_SOURCE_DIR}/src/parser/SV3_1aSplitterParser.cpp
  ${PROJECT_SOURCE_DIR}/src/parser/SV3_1aSplitterParserListener.cpp
  ${PROJECT_SOURCE_DIR}/src/SourceCompile/VObjectTypes.cpp
  ${PROJECT_SOURCE_DIR}/src/API/*.cpp
  ${PROJECT_SOURCE_DIR}/src/Design/*.cpp
  ${PROJECT_SOURCE_DIR}/src/Library/*.cpp
  ${PROJECT_SOURCE_DIR}/src/SourceCompile/AnalyzeFile.cpp
  ${PROJECT_SOURCE_DIR}/src/SourceCompile/Compiler.cpp
  ${PROJECT_SOURCE_DIR}/src/SourceCompile/PreprocessFile.cpp
  ${PROJECT_SOURCE_DIR}/src/SourceCompile/SymbolTable.cpp
  ${PROJECT_SOURCE_DIR}/src/SourceCompile/AntlrParserErrorListener.cpp
  ${PROJECT_SOURCE_DIR}/src/SourceCompile/CompileSourceFile.cpp
  ${PROJECT_SOURCE_DIR}/src/SourceCompile/PythonListen.cpp
  ${PROJECT_SOURCE_DIR}/src/SourceCompile/AntlrParserHandler.cpp
  ${PROJECT_SOURCE_DIR}/src/SourceCompile/LoopCheck.cpp
  ${PROJECT_SOURCE_DIR}/src/SourceCompile/SV3_1aPpTreeShapeListener.cpp
  ${PROJECT_SOURCE_DIR}/src/SourceCompile/SV3_1aPpTreeListenerHelper.cpp
  ${PROJECT_SOURCE_DIR}/src/SourceCompile/CommonListenerHelper.cpp
  ${PROJECT_SOURCE_DIR}/src/SourceCompile/CheckCompile.cpp
  ${PROJECT_SOURCE_DIR}/src/SourceCompile/MacroInfo.cpp
  ${PROJECT_SOURCE_DIR}/src/SourceCompile/SV3_1aTreeShapeHelper.cpp
  ${PROJECT_SOURCE_DIR}/src/SourceCompile/CompilationUnit.cpp
  ${PROJECT_SOURCE_DIR}/src/SourceCompile/ParseFile.cpp
  ${PROJECT_SOURCE_DIR}/src/SourceCompile/SV3_1aTreeShapeListener.cpp
  ${PROJECT_SOURCE_DIR}/src/DesignCompile/*.cpp
  ${PROJECT_SOURCE_DIR}/src/Testbench/*.cpp
  ${PROJECT_SOURCE_DIR}/src/CommandLine/*.cpp
  ${PROJECT_SOURCE_DIR}/src/Common/*.cpp
  ${PROJECT_SOURCE_DIR}/src/ErrorReporting/*.cpp
  ${PROJECT_SOURCE_DIR}/src/Utils/*.cpp
  ${PROJECT_SOURCE_DIR}/src/Cache/*.cpp
  ${PROJECT_SOURCE_DIR}/src/Config/*.cpp
  ${PROJECT_SOURCE_DIR}/src/Expression/*.cpp
  ${PROJECT_SOURCE_DIR}/src/Package/*.cpp)

set(SURELOG_PUBLIC_HEADERS ${PROJECT_SOURCE_DIR}/src/surelog.h)

add_library(surelog STATIC ${surelog_SRC})
set_target_properties(surelog PROPERTIES PUBLIC_HEADER
                                         "${SURELOG_PUBLIC_HEADERS}")

add_executable(surelog-bin ${PROJECT_SOURCE_DIR}/src/main.cpp)
set_target_properties(surelog-bin PROPERTIES OUTPUT_NAME surelog)

add_executable(hellosureworld ${PROJECT_SOURCE_DIR}/src/hellosureworld.cpp)

add_dependencies(surelog-bin surelog)
add_dependencies(surelog flatc)
add_dependencies(surelog antlr4_static)
add_dependencies(surelog flatbuffers)
add_dependencies(GenerateSerializer uhdm)
add_dependencies(GenerateParser antlr4_static)
add_dependencies(surelog GenerateParser)
add_dependencies(surelog GenerateSerializer)

if(NOT NO_TCMALLOC)
  set(TCMALLOC_LIBRARY tcmalloc)
endif(NOT NO_TCMALLOC)

set(ALL_LIBRARIES_FOR_SURELOG
    surelog
    ${PYTHON_LIBRARIES}
    -L${PROJECT_SOURCE_DIR}/dist/
    libantlr4-runtime.a
    -L${PROJECT_SOURCE_DIR}/build/third_party/flatbuffers
    libflatbuffers.a
    -L${PROJECT_SOURCE_DIR}/build/third_party/UHDM
    libuhdm.a
    capnp
    kj
    dl
    util
    m
    rt
    pthread
    ${TCMALLOC_LIBRARY})

# Linkage instructions
target_link_libraries(surelog-bin ${ALL_LIBRARIES_FOR_SURELOG})

add_dependencies(hellosureworld surelog)
add_dependencies(hellosureworld flatc)
add_dependencies(hellosureworld antlr4_static)
add_dependencies(hellosureworld flatbuffers)
add_dependencies(hellosureworld GenerateParser)
add_dependencies(hellosureworld GenerateSerializer)
target_link_libraries(hellosureworld ${ALL_LIBRARIES_FOR_SURELOG})

# Creation of the distribution directory, Precompiled package creation
add_custom_command(
  TARGET surelog-bin
  POST_BUILD
  COMMAND echo "       Creating staging for precompiled packages"
  COMMAND mkdir -p ${CMAKE_BINARY_DIR}/dist/${CMAKE_BUILD_TYPE}/sv
  COMMAND mkdir -p ${CMAKE_BINARY_DIR}/dist/${CMAKE_BUILD_TYPE}/python
  COMMAND cp -f ${CMAKE_BINARY_DIR}/../src/API/builtin.sv
          ${CMAKE_BINARY_DIR}/dist/${CMAKE_BUILD_TYPE}/sv
  COMMAND ln -fs ${CMAKE_BINARY_DIR}/../third_party/UVM/ovm-2.1.2 ovm-2.1.2
  COMMAND ln -fs ${CMAKE_BINARY_DIR}/../third_party/UVM/uvm-1.2 uvm-1.2
  COMMAND ln -fs ${CMAKE_BINARY_DIR}/../third_party/UVM/vmm-1.1.1a vmm-1.1.1a
  COMMAND rm -rf slpp_all slpp_unit
  COMMAND cp -f ${CMAKE_BINARY_DIR}/../src/API/slSV3_1aPythonListener.py
          ${CMAKE_BINARY_DIR}/dist/${CMAKE_BUILD_TYPE}/python/
  COMMAND cp -f ${CMAKE_BINARY_DIR}/../src/API/slformatmsg.py
          ${CMAKE_BINARY_DIR}/dist/${CMAKE_BUILD_TYPE}/python/slformatmsg.py
  COMMAND cp -f ${CMAKE_BINARY_DIR}/../src/API/slwaivers.py
          ${CMAKE_BINARY_DIR}/dist/${CMAKE_BUILD_TYPE}/python/
  COMMAND echo "       Creating OVM precompiled package..."
  COMMAND
    ${CMAKE_RUNTIME_OUTPUT_DIRECTORY}/surelog -nobuiltin -createcache
    +incdir+ovm-2.1.2/src/ +incdir+vmm-1.1.1a/sv ovm-2.1.2/src/ovm_pkg.sv
    -writepp -mt 0 -parse -nocomp -noelab -nostdout
  COMMAND echo "       Creating UVM precompiled package..."
  COMMAND
    ${CMAKE_RUNTIME_OUTPUT_DIRECTORY}/surelog -nobuiltin -createcache
    +incdir+.+uvm-1.2/src/ uvm-1.2/src/uvm_pkg.sv -writepp -mt 0 -parse -nocomp
    -noelab -nostdout
  COMMAND echo "       Packages created"
  WORKING_DIRECTORY "${CMAKE_BINARY_DIR}")

# Installation target
install(TARGETS surelog-bin RUNTIME DESTINATION ${CMAKE_INSTALL_BINDIR})
install(
  TARGETS surelog
  ARCHIVE DESTINATION ${CMAKE_INSTALL_LIBDIR}/surelog
  PUBLIC_HEADER DESTINATION ${CMAKE_INSTALL_INCLUDEDIR}/surelog)
install(
  DIRECTORY ${CMAKE_BINARY_DIR}/dist/${CMAKE_BUILD_TYPE}/python
            ${CMAKE_BINARY_DIR}/dist/${CMAKE_BUILD_TYPE}/sv
            ${CMAKE_BINARY_DIR}/dist/${CMAKE_BUILD_TYPE}/pkg
  DESTINATION ${CMAKE_INSTALL_LIBDIR}/surelog)
install(FILES ${PROJECT_SOURCE_DIR}/src/CommandLine/CommandLineParser.h
        DESTINATION ${CMAKE_INSTALL_INCLUDEDIR}/surelog/CommandLine)
install(FILES ${PROJECT_SOURCE_DIR}/src/SourceCompile/SymbolTable.h
              ${PROJECT_SOURCE_DIR}/src/SourceCompile/VObjectTypes.h
        DESTINATION ${CMAKE_INSTALL_INCLUDEDIR}/surelog/SourceCompile)
install(
  FILES ${PROJECT_SOURCE_DIR}/src/ErrorReporting/Location.h
        ${PROJECT_SOURCE_DIR}/src/ErrorReporting/Error.h
        ${PROJECT_SOURCE_DIR}/src/ErrorReporting/ErrorDefinition.h
        ${PROJECT_SOURCE_DIR}/src/ErrorReporting/ErrorContainer.h
        ${PROJECT_SOURCE_DIR}/src/ErrorReporting/Report.h
        ${PROJECT_SOURCE_DIR}/src/ErrorReporting/Waiver.h
  DESTINATION ${CMAKE_INSTALL_INCLUDEDIR}/surelog/ErrorReporting)
install(
  FILES ${PROJECT_SOURCE_DIR}/dist/libantlr4-runtime.a
        ${PROJECT_SOURCE_DIR}/build/third_party/flatbuffers/libflatbuffers.a
        ${PROJECT_SOURCE_DIR}/build/third_party/UHDM/libuhdm.a
  DESTINATION ${CMAKE_INSTALL_LIBDIR}/surelog)
install(
  FILES ${PROJECT_SOURCE_DIR}/src/API/PythonAPI.h
        ${PROJECT_SOURCE_DIR}/src/API/SLAPI.h
        ${PROJECT_SOURCE_DIR}/src/API/Surelog.h
  DESTINATION ${CMAKE_INSTALL_INCLUDEDIR}/surelog/API)
install(FILES ${PROJECT_SOURCE_DIR}/src/Common/ClockingBlockHolder.h
              ${PROJECT_SOURCE_DIR}/src/Common/PortNetHolder.h
        DESTINATION ${CMAKE_INSTALL_INCLUDEDIR}/surelog/Common)
install(FILES ${PROJECT_SOURCE_DIR}/src/DesignCompile/CompileHelper.h
        DESTINATION ${CMAKE_INSTALL_INCLUDEDIR}/surelog/DesignCompile)
install(
  FILES ${PROJECT_SOURCE_DIR}/src/Design/ClockingBlock.h
        ${PROJECT_SOURCE_DIR}/src/Design/Design.h
        ${PROJECT_SOURCE_DIR}/src/Design/Instance.h
        ${PROJECT_SOURCE_DIR}/src/Design/Signal.h
        ${PROJECT_SOURCE_DIR}/src/Design/ValuedComponentI.h
        ${PROJECT_SOURCE_DIR}/src/Design/DataType.h
        ${PROJECT_SOURCE_DIR}/src/Design/Enum.h
        ${PROJECT_SOURCE_DIR}/src/Design/ModuleDefinition.h
        ${PROJECT_SOURCE_DIR}/src/Design/Statement.h
        ${PROJECT_SOURCE_DIR}/src/Design/VObject.h
        ${PROJECT_SOURCE_DIR}/src/Design/DefParam.h
        ${PROJECT_SOURCE_DIR}/src/Design/FileCNodeId.h
        ${PROJECT_SOURCE_DIR}/src/Design/ModuleInstance.h
        ${PROJECT_SOURCE_DIR}/src/Design/Task.h
        ${PROJECT_SOURCE_DIR}/src/Design/DesignComponent.h
        ${PROJECT_SOURCE_DIR}/src/Design/FileContent.h
        ${PROJECT_SOURCE_DIR}/src/Design/Parameter.h
        ${PROJECT_SOURCE_DIR}/src/Design/TfPortItem.h
        ${PROJECT_SOURCE_DIR}/src/Design/DesignElement.h
        ${PROJECT_SOURCE_DIR}/src/Design/Function.h
        ${PROJECT_SOURCE_DIR}/src/Design/Scope.h
        ${PROJECT_SOURCE_DIR}/src/Design/TimeInfo.h
        ${PROJECT_SOURCE_DIR}/src/Design/ModPort.h
  DESTINATION ${CMAKE_INSTALL_INCLUDEDIR}/surelog/Design)
install(
  FILES ${PROJECT_SOURCE_DIR}/src/Testbench/ClassDefinition.h
        ${PROJECT_SOURCE_DIR}/src/Testbench/CoverGroupDefinition.h
        ${PROJECT_SOURCE_DIR}/src/Testbench/Property.h
        ${PROJECT_SOURCE_DIR}/src/Testbench/Variable.h
        ${PROJECT_SOURCE_DIR}/src/Testbench/ClassObject.h
        ${PROJECT_SOURCE_DIR}/src/Testbench/FunctionMethod.h
        ${PROJECT_SOURCE_DIR}/src/Testbench/TaskMethod.h
        ${PROJECT_SOURCE_DIR}/src/Testbench/Constraint.h
        ${PROJECT_SOURCE_DIR}/src/Testbench/Program.h
        ${PROJECT_SOURCE_DIR}/src/Testbench/TypeDef.h
  DESTINATION ${CMAKE_INSTALL_INCLUDEDIR}/surelog/Testbench)
install(FILES ${PROJECT_SOURCE_DIR}/src/Package/Package.h
        DESTINATION ${CMAKE_INSTALL_INCLUDEDIR}/surelog/Package)
install(FILES ${PROJECT_SOURCE_DIR}/src/Library/Library.h
              ${PROJECT_SOURCE_DIR}/src/Library/LibrarySet.h
        DESTINATION ${CMAKE_INSTALL_INCLUDEDIR}/surelog/Library)
install(FILES ${PROJECT_SOURCE_DIR}/src/Config/Config.h
              ${PROJECT_SOURCE_DIR}/src/Config/ConfigSet.h
        DESTINATION ${CMAKE_INSTALL_INCLUDEDIR}/surelog/Config)
install(
  FILES ${PROJECT_SOURCE_DIR}/src/Expression/ExprBuilder.h
        ${PROJECT_SOURCE_DIR}/src/Expression/Expr.h
        ${PROJECT_SOURCE_DIR}/src/Expression/Value.h
  DESTINATION ${CMAKE_INSTALL_INCLUDEDIR}/surelog/Expression)
