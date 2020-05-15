# -*- mode:cmake -*-
cmake_minimum_required(VERSION 3.15)

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

option(
  WITH_LIBCXX
  "Building with clang++ and libc++(in Linux). To enable with: -DWITH_LIBCXX=On"
  On)

project(SURELOG)

# NOTE: Policy changes has to happen before adding any subprojects
cmake_policy(SET CMP0091 NEW)
set(CMAKE_MSVC_RUNTIME_LIBRARY "MultiThreaded$<$<CONFIG:Debug>:Debug>")

set(FLATBUFFERS_BUILD_TESTS OFF CACHE BOOL "Skip flatbuffers' tests")
add_subdirectory(third_party/flatbuffers EXCLUDE_FROM_ALL)
add_subdirectory(third_party/antlr4/runtime/Cpp EXCLUDE_FROM_ALL)
add_subdirectory(third_party/UHDM)
add_subdirectory(third_party/googletest EXCLUDE_FROM_ALL)

set(CMAKE_CXX_STANDARD 17)
set(CMAKE_CXX_STANDARD_REQUIRED ON)
set(CMAKE_EXPORT_COMPILE_COMMANDS ON)

# NOTE: Set the global output directories after the subprojects have had their go at it
set(CMAKE_ARCHIVE_OUTPUT_DIRECTORY ${CMAKE_CURRENT_BINARY_DIR}/lib)
set(CMAKE_LIBRARY_OUTPUT_DIRECTORY ${CMAKE_CURRENT_BINARY_DIR}/bin)
set(CMAKE_RUNTIME_OUTPUT_DIRECTORY ${CMAKE_CURRENT_BINARY_DIR}/bin)

find_package(SWIG REQUIRED)

# Python
find_package(PythonLibs 3.3 REQUIRED)
include_directories(${PYTHON_INCLUDE_DIRS})
message(STATUS "PYTHON_LIBRARIES = ${PYTHON_LIBRARIES}")
message(STATUS "PYTHON_EXECUTABLE = ${PYTHON_EXECUTABLE}")
message(STATUS "PYTHON_INCLUDE_DIRS = ${PYTHON_INCLUDE_DIRS}")

# Includes
include_directories("${PROJECT_SOURCE_DIR}/third_party/antlr4/runtime/Cpp/runtime/src/")
include_directories("${PROJECT_SOURCE_DIR}/third_party/flatbuffers/include/")
include_directories("${PROJECT_SOURCE_DIR}/third_party/UHDM/include/")
include_directories("${PROJECT_SOURCE_DIR}/third_party/UHDM/")
include_directories("${PROJECT_SOURCE_DIR}/third_party/UHDM/headers/")
include_directories("${PROJECT_SOURCE_DIR}/third_party/UHDM/src/")
include_directories("${PROJECT_SOURCE_DIR}/third_party/UHDM/third_party/capnproto/c++/src/")
include_directories("${PROJECT_SOURCE_DIR}/third_party/UHDM/third_party/UHDM/src/")
include_directories("${PROJECT_SOURCE_DIR}/third_party/googletest/googletest/include/")
include_directories("${PROJECT_SOURCE_DIR}/third_party/googletest/googlemock/include/")

# Use tcmalloc if installed and not NO_TCMALLOC is on. TODO: don't use negative
# names, but positive. -DWITH_TCMALLOC=Off is easier to understand than
# -DNO_TCMALLOC=On
if(NOT NO_TCMALLOC)
  find_library(TCMALLOC_LIBRARY NAMES tcmalloc)
  if(TCMALLOC_LIBRARY)
    message(
      WARNING
        "USING TCMALLOC, IF YOU HAVE RUNTIME ISSUES, DISABLE -DNO_TCMALLOC=On")
    message("-- Found tcmalloc: ${TCMALLOC_LIBRARY}")
    set(TCMALLOC_COMPILE_OPTIONS
        "-fno-builtin-malloc -fno-builtin-calloc -fno-builtin-realloc -fno-builtin-free"
    )
  endif()
endif()

set(CMAKE_CXX_FLAGS
    "${CMAKE_CXX_FLAGS} ${TCMALLOC_COMPILE_OPTIONS} ${MY_CXX_WARNING_FLAGS}")

if(MSVC)
    set(CMAKE_CXX_FLAGS_DEBUG
        "${CMAKE_CXX_FLAGS_DEBUG} ${TCMALLOC_COMPILE_OPTIONS} /W0 /bigobj /DPLI_DLLISPEC= /DANTLR4CPP_STATIC /D_CRT_NONSTDC_NO_WARNINGS ${MY_CXX_WARNING_FLAGS}"
    )
    set(CMAKE_CXX_FLAGS_RELEASE
        "${CMAKE_CXX_FLAGS_RELEASE} ${TCMALLOC_COMPILE_OPTIONS}/W0 /bigobj /DPLI_DLLISPEC= /DANTLR4CPP_STATIC /D_CRT_NONSTDC_NO_WARNINGS ${MY_CXX_WARNING_FLAGS}"
    )
    set(CMAKE_EXE_LINKER_FLAGS /STACK:8388608)  # 8MB stack size
else()
    set(CMAKE_CXX_FLAGS_DEBUG
        "${CMAKE_CXX_FLAGS_DEBUG} ${TCMALLOC_COMPILE_OPTIONS} -Wall -O0 -g ${MY_CXX_WARNING_FLAGS}"
    )
    set(CMAKE_CXX_FLAGS_RELEASE
        "${CMAKE_CXX_FLAGS_RELEASE} ${TCMALLOC_COMPILE_OPTIONS} -Wall -O3 -DNDEBUG ${MY_CXX_WARNING_FLAGS}"
    )
endif()

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
  WORKING_DIRECTORY "${CMAKE_CURRENT_BINARY_DIR}"
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
  COMMAND tclsh SourceCompile/generate_parser_listener.tcl ;
  COMMAND tclsh API/generate_python_listener_api.tcl ;
  COMMAND echo "       Python API Generation..."
  COMMAND ${SWIG_EXECUTABLE} -c++ -python -o API/slapi_wrap.cxx API/slapi_scripts.i ;
  COMMAND tclsh API/embed_python_api.tcl
  COMMAND touch ${PROJECT_SOURCE_DIR}/src/SourceCompile/dummy2
  COMMAND echo "       Code Generation completed"
  DEPENDS ${PROJECT_SOURCE_DIR}/grammar/SV3_1aPpLexer.g4
          ${PROJECT_SOURCE_DIR}/grammar/SV3_1aLexer.g4
          ${PROJECT_SOURCE_DIR}/grammar/SV3_1aSplitterLexer.g4
          ${PROJECT_SOURCE_DIR}/grammar/SV3_1aPpParser.g4
          ${PROJECT_SOURCE_DIR}/grammar/SV3_1aParser.g4
          ${PROJECT_SOURCE_DIR}/grammar/SV3_1aSplitterParser.g4
          ${PROJECT_SOURCE_DIR}/src/API/slapi_scripts.i
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
  ${PROJECT_SOURCE_DIR}/src/DesignCompile/Builtin.cpp
  ${PROJECT_SOURCE_DIR}/src/DesignCompile/CompileClass.cpp
  ${PROJECT_SOURCE_DIR}/src/DesignCompile/CompileDesign.cpp
  ${PROJECT_SOURCE_DIR}/src/DesignCompile/CompileFileContent.cpp
  ${PROJECT_SOURCE_DIR}/src/DesignCompile/CompileHelper.cpp
  ${PROJECT_SOURCE_DIR}/src/DesignCompile/CompileExpression.cpp
  ${PROJECT_SOURCE_DIR}/src/DesignCompile/CompileStmt.cpp
  ${PROJECT_SOURCE_DIR}/src/DesignCompile/CompileType.cpp
  ${PROJECT_SOURCE_DIR}/src/DesignCompile/CompileModule.cpp
  ${PROJECT_SOURCE_DIR}/src/DesignCompile/CompilePackage.cpp
  ${PROJECT_SOURCE_DIR}/src/DesignCompile/CompileProgram.cpp
  ${PROJECT_SOURCE_DIR}/src/DesignCompile/CompileStep.cpp
  ${PROJECT_SOURCE_DIR}/src/DesignCompile/CompileToolbox.cpp
  ${PROJECT_SOURCE_DIR}/src/DesignCompile/DesignElaboration.cpp
  ${PROJECT_SOURCE_DIR}/src/DesignCompile/ElaborationStep.cpp
  ${PROJECT_SOURCE_DIR}/src/DesignCompile/NetlistElaboration.cpp
  ${PROJECT_SOURCE_DIR}/src/DesignCompile/PackageAndRootElaboration.cpp
  ${PROJECT_SOURCE_DIR}/src/DesignCompile/ResolveSymbols.cpp
  ${PROJECT_SOURCE_DIR}/src/DesignCompile/TestbenchElaboration.cpp
  ${PROJECT_SOURCE_DIR}/src/DesignCompile/UhdmWriter.cpp
  ${PROJECT_SOURCE_DIR}/src/DesignCompile/UhdmChecker.cpp
  ${PROJECT_SOURCE_DIR}/src/DesignCompile/UVMElaboration.cpp
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
add_executable(hellouhdm ${PROJECT_SOURCE_DIR}/src/hellouhdm.cpp)

target_link_libraries(surelog-bin PUBLIC surelog)
target_link_libraries(surelog PUBLIC antlr4_static)
target_link_libraries(surelog PUBLIC flatbuffers)
target_link_libraries(surelog PUBLIC uhdm)
add_dependencies(surelog flatc)
add_dependencies(GenerateSerializer uhdm)
add_dependencies(GenerateParser antlr4_static)
add_dependencies(surelog GenerateParser)
add_dependencies(surelog GenerateSerializer)

target_link_libraries(surelog PRIVATE ${PYTHON_LIBRARIES})
target_link_libraries(surelog PRIVATE ${TCMALLOC_LIBRARY})

if (UNIX)
  target_link_libraries(surelog PRIVATE dl)
  target_link_libraries(surelog PRIVATE util)
  target_link_libraries(surelog PRIVATE m)
  target_link_libraries(surelog PRIVATE rt)
  target_link_libraries(surelog PRIVATE pthread)
endif()

# Unit tests
enable_testing()

add_executable(CompileHelper-Test EXCLUDE_FROM_ALL
  ${PROJECT_SOURCE_DIR}/src/DesignCompile/CompileHelper_test.cpp
)
target_link_libraries(CompileHelper-Test
  PRIVATE surelog
  PRIVATE gtest
  PRIVATE gmock
  PRIVATE gtest_main)
#add_test(NAME test_CompileHelper COMMAND CompileHelper-Test WORKING_DIRECTORY ${CMAKE_CURRENT_BINARY_DIR} )

add_custom_target(UnitTests
  DEPENDS CompileHelper-Test
  # Add further test binaries above
)

target_link_libraries(hellosureworld surelog)
target_link_libraries(hellouhdm surelog)

# Creation of the distribution directory, Precompiled package creation
add_custom_command(
  TARGET surelog-bin
  POST_BUILD
  COMMAND echo "       Creating staging for precompiled packages"
  COMMAND mkdir -p ${CMAKE_RUNTIME_OUTPUT_DIRECTORY}/sv
  COMMAND mkdir -p ${CMAKE_RUNTIME_OUTPUT_DIRECTORY}/python
  COMMAND ln -fs ${PROJECT_SOURCE_DIR}/third_party/UVM/ovm-2.1.2 ovm-2.1.2
  COMMAND ln -fs ${PROJECT_SOURCE_DIR}/third_party/UVM/1800.2-2017-1.0 1800.2-2017-1.0
  COMMAND ln -fs ${PROJECT_SOURCE_DIR}/third_party/UVM/vmm-1.1.1a vmm-1.1.1a
  COMMAND rm -rf slpp_all slpp_unit
  COMMAND cp -f ${PROJECT_SOURCE_DIR}/src/API/builtin.sv ${CMAKE_RUNTIME_OUTPUT_DIRECTORY}/sv/builtin.sv
  COMMAND cp -f ${PROJECT_SOURCE_DIR}/src/API/slSV3_1aPythonListener.py
          ${CMAKE_RUNTIME_OUTPUT_DIRECTORY}/python/slSV3_1aPythonListener.py
  COMMAND cp -f ${PROJECT_SOURCE_DIR}/src/API/slformatmsg.py
          ${CMAKE_RUNTIME_OUTPUT_DIRECTORY}/python/slformatmsg.py
  COMMAND cp -f ${PROJECT_SOURCE_DIR}/src/API/slwaivers.py
          ${CMAKE_RUNTIME_OUTPUT_DIRECTORY}/python/slwaivers.py
  COMMAND echo "       Staging created"
  WORKING_DIRECTORY "${CMAKE_RUNTIME_OUTPUT_DIRECTORY}")

add_custom_target(PrecompileOVM DEPENDS ${CMAKE_RUNTIME_OUTPUT_DIRECTORY}/pkg/work/ovm_pkg.sv.slpa)
add_custom_command(
  #TARGET surelog-bin
  #POST_BUILD
  OUTPUT  ${CMAKE_RUNTIME_OUTPUT_DIRECTORY}/pkg/work/ovm_pkg.sv.slpa
  COMMAND echo "       Creating OVM precompiled package..."
  DEPENDS surelog-bin
  COMMAND
    ${CMAKE_RUNTIME_OUTPUT_DIRECTORY}/surelog -nobuiltin -createcache
    +incdir+ovm-2.1.2/src/ +incdir+vmm-1.1.1a/sv ovm-2.1.2/src/ovm_pkg.sv
    -writepp -mt 0 -parse -nocomp -noelab -nostdout  
  COMMAND echo "       Package OVM created"
  WORKING_DIRECTORY "${CMAKE_RUNTIME_OUTPUT_DIRECTORY}")

add_custom_target(PrecompileUVM DEPENDS ${CMAKE_RUNTIME_OUTPUT_DIRECTORY}/pkg/work/uvm_pkg.sv.slpa)
add_custom_command(
  #TARGET surelog-bin
  #POST_BUILD
  OUTPUT  ${CMAKE_RUNTIME_OUTPUT_DIRECTORY}/pkg/work/uvm_pkg.sv.slpa
  COMMAND echo "       Creating UVM precompiled package..."
  DEPENDS surelog-bin
  COMMAND
    ${CMAKE_RUNTIME_OUTPUT_DIRECTORY}/surelog -nobuiltin -createcache
    +incdir+.+1800.2-2017-1.0/src/ 1800.2-2017-1.0/src/uvm_pkg.sv -writepp -mt 0
    -parse -nocomp -noelab -nostdout
  COMMAND echo "       Package UVM created"
  WORKING_DIRECTORY "${CMAKE_RUNTIME_OUTPUT_DIRECTORY}")
add_dependencies(hellosureworld PrecompileOVM)
add_dependencies(hellosureworld PrecompileUVM)

# Installation target
install(TARGETS surelog-bin RUNTIME DESTINATION ${CMAKE_INSTALL_BINDIR})
install(
  TARGETS surelog
  ARCHIVE DESTINATION ${CMAKE_INSTALL_LIBDIR}/surelog
  PUBLIC_HEADER DESTINATION ${CMAKE_INSTALL_INCLUDEDIR}/surelog)
install(
  DIRECTORY ${CMAKE_RUNTIME_OUTPUT_DIRECTORY}/python
            ${CMAKE_RUNTIME_OUTPUT_DIRECTORY}/sv
            ${CMAKE_RUNTIME_OUTPUT_DIRECTORY}/pkg
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
        ${CMAKE_BINARY_DIR}/third_party/flatbuffers/libflatbuffers.a
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
        ${PROJECT_SOURCE_DIR}/src/Design/Struct.h
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
        ${PROJECT_SOURCE_DIR}/src/Design/Netlist.h
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

