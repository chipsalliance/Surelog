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

set(UHDM_BUILD_TESTS OFF CACHE BOOL "Skip UHDM tests")
add_subdirectory(third_party/UHDM)
add_subdirectory(third_party/googletest EXCLUDE_FROM_ALL)

set(CMAKE_CXX_STANDARD 17)
set(CMAKE_CXX_STANDARD_REQUIRED ON)
set(CMAKE_EXPORT_COMPILE_COMMANDS ON)

# NOTE: Set the global output directories after the subprojects have had their go at it
set(CMAKE_ARCHIVE_OUTPUT_DIRECTORY ${CMAKE_CURRENT_BINARY_DIR}/lib)
set(CMAKE_LIBRARY_OUTPUT_DIRECTORY ${CMAKE_CURRENT_BINARY_DIR}/bin)
set(CMAKE_RUNTIME_OUTPUT_DIRECTORY ${CMAKE_CURRENT_BINARY_DIR}/bin)

find_package(SWIG 3.0 REQUIRED)

# Python
find_package(Python3 3.3 REQUIRED COMPONENTS Interpreter Development)
message(STATUS "Python3_LIBRARIES = ${Python3_LIBRARIES}")
message(STATUS "Python3_EXECUTABLE = ${Python3_EXECUTABLE}")
message(STATUS "Python3_INCLUDE_DIRS = ${Python3_INCLUDE_DIRS}")
message(STATUS "Python3_RUNTIME_LIBRARY_DIRS = ${Python3_RUNTIME_LIBRARY_DIRS}")

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
include_directories(${Python3_INCLUDE_DIRS}) # Keep this at the end

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

if(MSVC OR WIN32)
  add_compile_definitions(ANTLR4CPP_STATIC)
endif()

if(MSVC)
  add_compile_definitions(_CRT_NONSTDC_NO_WARNINGS)

  set(CMAKE_CXX_FLAGS_DEBUG
      "${CMAKE_CXX_FLAGS_DEBUG} ${TCMALLOC_COMPILE_OPTIONS} /Zc:__cplusplus /W0 /bigobj ${MY_CXX_WARNING_FLAGS}"
  )
  set(CMAKE_CXX_FLAGS_RELWITHDEBINFO
      "${CMAKE_CXX_FLAGS_RELEASE} ${TCMALLOC_COMPILE_OPTIONS} /Zc:__cplusplus /W0 /bigobj ${MY_CXX_WARNING_FLAGS}"
  )
  set(CMAKE_CXX_FLAGS_RELEASE
      "${CMAKE_CXX_FLAGS_RELEASE} ${TCMALLOC_COMPILE_OPTIONS} /Zc:__cplusplus /W0 /bigobj ${MY_CXX_WARNING_FLAGS}"
  )
  set(CMAKE_EXE_LINKER_FLAGS /STACK:8388608)  # 8MB stack size
else()
  if(DEFINED ENV{MSYSTEM})
    # Under MSYS some files are too large to build without additional flags
    set(MSYS_COMPILE_OPTIONS "-m64 -Wa,-mbig-obj")
  endif()

  set(CMAKE_CXX_FLAGS_DEBUG
      "${CMAKE_CXX_FLAGS_DEBUG} ${TCMALLOC_COMPILE_OPTIONS} -Wall -O0 -g ${MSYS_COMPILE_OPTIONS} ${MY_CXX_WARNING_FLAGS}"
  )
  set(CMAKE_CXX_FLAGS_RELEASE
      "${CMAKE_CXX_FLAGS_RELEASE} ${TCMALLOC_COMPILE_OPTIONS} -Wall -O3 ${MSYS_COMPILE_OPTIONS} -DNDEBUG ${MY_CXX_WARNING_FLAGS}"
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
find_package(Java REQUIRED COMPONENTS Runtime)
set(ANTLR_JAR_LOCATION
    ${PROJECT_SOURCE_DIR}/third_party/antlr4/antlr-4.9.1-complete.jar)

add_custom_target(GenerateParser DEPENDS
  ${PROJECT_SOURCE_DIR}/src/parser/generated-parsers.tstamp
  ${PROJECT_SOURCE_DIR}/src/SourceCompile/VObjectTypes.cpp
  ${PROJECT_SOURCE_DIR}/src/API/slapi.py)

set(surelog_grammars
  ${PROJECT_SOURCE_DIR}/grammar/SV3_1aLexer.g4
  ${PROJECT_SOURCE_DIR}/grammar/SV3_1aParser.g4
  ${PROJECT_SOURCE_DIR}/grammar/SV3_1aPpLexer.g4
  ${PROJECT_SOURCE_DIR}/grammar/SV3_1aPpParser.g4
  ${PROJECT_SOURCE_DIR}/grammar/SV3_1aSplitterLexer.g4
  ${PROJECT_SOURCE_DIR}/grammar/SV3_1aSplitterParser.g4
)

set(surelog_grammars-GENERATED_SRC
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
)

add_custom_command(
  OUTPUT ${surelog_grammars-GENERATED_SRC} ${PROJECT_SOURCE_DIR}/src/parser/generated-parsers.tstamp
  WORKING_DIRECTORY "${PROJECT_SOURCE_DIR}/grammar/"
  COMMAND echo "---------- Parser generation..."
  COMMAND ${CMAKE_COMMAND} -E make_directory ${PROJECT_SOURCE_DIR}/src/parser/
  # We can't use ${surelog_grammars} here, as then the generated files would
  # contain a reference to the full path-name (issue #88).
  # Unfortunately, cmake does not provide simple equivalents to
  # gmake's $(nodir $(surelog_grammars)).
  # So, we list them here all manually passing to the command.
  COMMAND java -jar ${ANTLR_JAR_LOCATION} -Werror -Dlanguage=Cpp
             -o ${PROJECT_SOURCE_DIR}/src/parser/
             SV3_1aLexer.g4    SV3_1aParser.g4
             SV3_1aPpLexer.g4  SV3_1aPpParser.g4
             SV3_1aSplitterLexer.g4  SV3_1aSplitterParser.g4
  DEPENDS ${surelog_grammars}
  COMMAND ${CMAKE_COMMAND} -E touch ${PROJECT_SOURCE_DIR}/src/parser/generated-parsers.tstamp
)

add_custom_command(
  OUTPUT ${PROJECT_SOURCE_DIR}/src/SourceCompile/VObjectTypes.h
         ${PROJECT_SOURCE_DIR}/src/SourceCompile/VObjectTypes.cpp
         ${PROJECT_SOURCE_DIR}/src/API/vobjecttypes_py.h
         ${PROJECT_SOURCE_DIR}/src/SourceCompile/SV3_1aTreeShapeListener.h
         ${PROJECT_SOURCE_DIR}/src/SourceCompile/SV3_1aPpTreeShapeListener.h
  DEPENDS ${PROJECT_SOURCE_DIR}/src/parser/generated-parsers.tstamp
          ${PROJECT_SOURCE_DIR}/src/SourceCompile/generate_parser_listener.tcl

  WORKING_DIRECTORY "${PROJECT_SOURCE_DIR}/src/"
  COMMAND echo "---------- VObjectTypes, Listener generation"
  COMMAND ${CMAKE_COMMAND} -E make_directory ${PROJECT_SOURCE_DIR}/src/SourceCompile
  COMMAND ${CMAKE_COMMAND} -E make_directory ${PROJECT_SOURCE_DIR}/src/API
  COMMAND tclsh SourceCompile/generate_parser_listener.tcl out_dir=${PROJECT_SOURCE_DIR}/src
)

add_custom_command(
  OUTPUT  ${PROJECT_SOURCE_DIR}/src/API/SV3_1aPythonListener.h
          ${PROJECT_SOURCE_DIR}/src/API/slSV3_1aPythonListener.py
          ${PROJECT_SOURCE_DIR}/src/API/slapi_wrap.cxx
          ${PROJECT_SOURCE_DIR}/src/API/slapi_scripts.h
          ${PROJECT_SOURCE_DIR}/src/API/slapi.py
  DEPENDS ${PROJECT_SOURCE_DIR}/src/API/slapi_scripts.i
          ${PROJECT_SOURCE_DIR}/src/API/vobjecttypes_py.h
          ${PROJECT_SOURCE_DIR}/src/parser/generated-parsers.tstamp
          ${PROJECT_SOURCE_DIR}/src/API/generate_python_listener_api.tcl
          ${PROJECT_SOURCE_DIR}/src/API/embed_python_api.tcl

  WORKING_DIRECTORY "${PROJECT_SOURCE_DIR}/src/"
  COMMAND echo "---------- Python API generation"
  COMMAND tclsh API/generate_python_listener_api.tcl
  COMMAND ${SWIG_EXECUTABLE} -c++ -python -o API/slapi_wrap.cxx API/slapi_scripts.i
  COMMAND tclsh API/embed_python_api.tcl
)

include_directories(${PROJECT_SOURCE_DIR}/src)

# Put source code here, files that are generated at build time in
# surelog_generated_SRC
set(surelog_SRC
  ${PROJECT_SOURCE_DIR}/src/API/PythonAPI.cpp
  ${PROJECT_SOURCE_DIR}/src/API/SLAPI.cpp
  ${PROJECT_SOURCE_DIR}/src/API/SV3_1aPythonListener.cpp
  ${PROJECT_SOURCE_DIR}/src/API/Surelog.cpp
  ${PROJECT_SOURCE_DIR}/src/Cache/Cache.cpp
  ${PROJECT_SOURCE_DIR}/src/Cache/PPCache.cpp
  ${PROJECT_SOURCE_DIR}/src/Cache/ParseCache.cpp
  ${PROJECT_SOURCE_DIR}/src/Cache/PythonAPICache.cpp
  ${PROJECT_SOURCE_DIR}/src/CommandLine/CommandLineParser.cpp
  ${PROJECT_SOURCE_DIR}/src/Common/ClockingBlockHolder.cpp
  ${PROJECT_SOURCE_DIR}/src/Common/PortNetHolder.cpp
  ${PROJECT_SOURCE_DIR}/src/Config/Config.cpp
  ${PROJECT_SOURCE_DIR}/src/Config/ConfigSet.cpp
  ${PROJECT_SOURCE_DIR}/src/Design/DataType.cpp
  ${PROJECT_SOURCE_DIR}/src/Design/DefParam.cpp
  ${PROJECT_SOURCE_DIR}/src/Design/Design.cpp
  ${PROJECT_SOURCE_DIR}/src/Design/DesignComponent.cpp
  ${PROJECT_SOURCE_DIR}/src/Design/DesignElement.cpp
  ${PROJECT_SOURCE_DIR}/src/Design/Enum.cpp
  ${PROJECT_SOURCE_DIR}/src/Design/FileContent.cpp
  ${PROJECT_SOURCE_DIR}/src/Design/Function.cpp
  ${PROJECT_SOURCE_DIR}/src/Design/ModPort.cpp
  ${PROJECT_SOURCE_DIR}/src/Design/ModuleDefinition.cpp
  ${PROJECT_SOURCE_DIR}/src/Design/ModuleInstance.cpp
  ${PROJECT_SOURCE_DIR}/src/Design/Netlist.cpp
  ${PROJECT_SOURCE_DIR}/src/Design/Parameter.cpp
  ${PROJECT_SOURCE_DIR}/src/Design/ParamAssign.cpp
  ${PROJECT_SOURCE_DIR}/src/Design/Scope.cpp
  ${PROJECT_SOURCE_DIR}/src/Design/Signal.cpp
  ${PROJECT_SOURCE_DIR}/src/Design/SimpleType.cpp
  ${PROJECT_SOURCE_DIR}/src/Design/DummyType.cpp
  ${PROJECT_SOURCE_DIR}/src/Design/Statement.cpp
  ${PROJECT_SOURCE_DIR}/src/Design/Struct.cpp
  ${PROJECT_SOURCE_DIR}/src/Design/Task.cpp
  ${PROJECT_SOURCE_DIR}/src/Design/TfPortItem.cpp
  ${PROJECT_SOURCE_DIR}/src/Design/TimeInfo.cpp
  ${PROJECT_SOURCE_DIR}/src/Design/Union.cpp
  ${PROJECT_SOURCE_DIR}/src/Design/VObject.cpp
  ${PROJECT_SOURCE_DIR}/src/Design/ValuedComponentI.cpp
  ${PROJECT_SOURCE_DIR}/src/DesignCompile/Builtin.cpp
  ${PROJECT_SOURCE_DIR}/src/DesignCompile/CompileAssertion.cpp
  ${PROJECT_SOURCE_DIR}/src/DesignCompile/CompileClass.cpp
  ${PROJECT_SOURCE_DIR}/src/DesignCompile/CompileDesign.cpp
  ${PROJECT_SOURCE_DIR}/src/DesignCompile/CompileExpression.cpp
  ${PROJECT_SOURCE_DIR}/src/DesignCompile/CompileFileContent.cpp
  ${PROJECT_SOURCE_DIR}/src/DesignCompile/CompileHelper.cpp
  ${PROJECT_SOURCE_DIR}/src/DesignCompile/CompileModule.cpp
  ${PROJECT_SOURCE_DIR}/src/DesignCompile/CompilePackage.cpp
  ${PROJECT_SOURCE_DIR}/src/DesignCompile/CompileProgram.cpp
  ${PROJECT_SOURCE_DIR}/src/DesignCompile/CompileStep.cpp
  ${PROJECT_SOURCE_DIR}/src/DesignCompile/CompileStmt.cpp
  ${PROJECT_SOURCE_DIR}/src/DesignCompile/CompileToolbox.cpp
  ${PROJECT_SOURCE_DIR}/src/DesignCompile/CompileType.cpp
  ${PROJECT_SOURCE_DIR}/src/DesignCompile/DesignElaboration.cpp
  ${PROJECT_SOURCE_DIR}/src/DesignCompile/ElaborationStep.cpp
  ${PROJECT_SOURCE_DIR}/src/DesignCompile/NetlistElaboration.cpp
  ${PROJECT_SOURCE_DIR}/src/DesignCompile/PackageAndRootElaboration.cpp
  ${PROJECT_SOURCE_DIR}/src/DesignCompile/ResolveSymbols.cpp
  ${PROJECT_SOURCE_DIR}/src/DesignCompile/TestbenchElaboration.cpp
  ${PROJECT_SOURCE_DIR}/src/DesignCompile/UVMElaboration.cpp
  ${PROJECT_SOURCE_DIR}/src/DesignCompile/UhdmChecker.cpp
  ${PROJECT_SOURCE_DIR}/src/DesignCompile/UhdmWriter.cpp
  ${PROJECT_SOURCE_DIR}/src/ErrorReporting/Error.cpp
  ${PROJECT_SOURCE_DIR}/src/ErrorReporting/ErrorContainer.cpp
  ${PROJECT_SOURCE_DIR}/src/ErrorReporting/ErrorDefinition.cpp
  ${PROJECT_SOURCE_DIR}/src/ErrorReporting/Location.cpp
  ${PROJECT_SOURCE_DIR}/src/ErrorReporting/Report.cpp
  ${PROJECT_SOURCE_DIR}/src/ErrorReporting/Waiver.cpp
  ${PROJECT_SOURCE_DIR}/src/Expression/ExprBuilder.cpp
  ${PROJECT_SOURCE_DIR}/src/Expression/Value.cpp
  ${PROJECT_SOURCE_DIR}/src/Library/AntlrLibParserErrorListener.cpp
  ${PROJECT_SOURCE_DIR}/src/Library/Library.cpp
  ${PROJECT_SOURCE_DIR}/src/Library/LibrarySet.cpp
  ${PROJECT_SOURCE_DIR}/src/Library/ParseLibraryDef.cpp
  ${PROJECT_SOURCE_DIR}/src/Library/SVLibShapeListener.cpp
  ${PROJECT_SOURCE_DIR}/src/Package/Package.cpp
  ${PROJECT_SOURCE_DIR}/src/Package/Precompiled.cpp
  ${PROJECT_SOURCE_DIR}/src/SourceCompile/AnalyzeFile.cpp
  ${PROJECT_SOURCE_DIR}/src/SourceCompile/AntlrParserErrorListener.cpp
  ${PROJECT_SOURCE_DIR}/src/SourceCompile/AntlrParserHandler.cpp
  ${PROJECT_SOURCE_DIR}/src/SourceCompile/CheckCompile.cpp
  ${PROJECT_SOURCE_DIR}/src/SourceCompile/CommonListenerHelper.cpp
  ${PROJECT_SOURCE_DIR}/src/SourceCompile/CompilationUnit.cpp
  ${PROJECT_SOURCE_DIR}/src/SourceCompile/CompileSourceFile.cpp
  ${PROJECT_SOURCE_DIR}/src/SourceCompile/Compiler.cpp
  ${PROJECT_SOURCE_DIR}/src/SourceCompile/LoopCheck.cpp
  ${PROJECT_SOURCE_DIR}/src/SourceCompile/MacroInfo.cpp
  ${PROJECT_SOURCE_DIR}/src/SourceCompile/ParseFile.cpp
  ${PROJECT_SOURCE_DIR}/src/SourceCompile/PreprocessFile.cpp
  ${PROJECT_SOURCE_DIR}/src/SourceCompile/PythonListen.cpp
  ${PROJECT_SOURCE_DIR}/src/SourceCompile/SV3_1aPpTreeListenerHelper.cpp
  ${PROJECT_SOURCE_DIR}/src/SourceCompile/SV3_1aPpTreeShapeListener.cpp
  ${PROJECT_SOURCE_DIR}/src/SourceCompile/SV3_1aTreeShapeHelper.cpp
  ${PROJECT_SOURCE_DIR}/src/SourceCompile/SV3_1aTreeShapeListener.cpp
  ${PROJECT_SOURCE_DIR}/src/SourceCompile/SymbolTable.cpp
  ${PROJECT_SOURCE_DIR}/src/Testbench/ClassDefinition.cpp
  ${PROJECT_SOURCE_DIR}/src/Testbench/ClassObject.cpp
  ${PROJECT_SOURCE_DIR}/src/Testbench/FunctionMethod.cpp
  ${PROJECT_SOURCE_DIR}/src/Testbench/Program.cpp
  ${PROJECT_SOURCE_DIR}/src/Testbench/Property.cpp
  ${PROJECT_SOURCE_DIR}/src/Testbench/TaskMethod.cpp
  ${PROJECT_SOURCE_DIR}/src/Testbench/TypeDef.cpp
  ${PROJECT_SOURCE_DIR}/src/Testbench/Variable.cpp
  ${PROJECT_SOURCE_DIR}/src/Utils/FileUtils.cpp
  ${PROJECT_SOURCE_DIR}/src/Utils/ParseUtils.cpp
  ${PROJECT_SOURCE_DIR}/src/Utils/StringUtils.cpp
  ${PROJECT_SOURCE_DIR}/src/Utils/NumUtils.cpp
  ${PROJECT_SOURCE_DIR}/src/Utils/Timer.cpp
)

# TODO: these generated sources should go to a directory that
# does not mess with the original source, e.g.
# ${CMAKE_CURRENT_BINARY_DIR}/gen-src
# That way, we also don't have/should have to check in the generated
# files.
set(surelog_generated_SRC
  # generated parser
  ${surelog_grammars-GENERATED_SRC}

  # Derived from parser generation.
  ${PROJECT_SOURCE_DIR}/src/SourceCompile/VObjectTypes.cpp)

foreach(gen_src ${surelog_generated_SRC})
  set_source_files_properties(${gen_src} PROPERTIES GENERATED TRUE)
endforeach()

set(SURELOG_PUBLIC_HEADERS ${PROJECT_SOURCE_DIR}/src/surelog.h)

add_library(surelog STATIC ${surelog_SRC} ${surelog_generated_SRC})
set_target_properties(surelog PROPERTIES PUBLIC_HEADER "${SURELOG_PUBLIC_HEADERS}")

add_executable(surelog-bin ${PROJECT_SOURCE_DIR}/src/main.cpp)
set_target_properties(surelog-bin PROPERTIES OUTPUT_NAME surelog)

add_executable(hellosureworld ${PROJECT_SOURCE_DIR}/src/hellosureworld.cpp)
add_executable(hellouhdm ${PROJECT_SOURCE_DIR}/src/hellouhdm.cpp)

if(MSVC OR WIN32)
  # We have two files named "surelog.lib" and both getting generated in the lib folder
  # One is the surelog.lib generated by the surelog target and the other is the one generated
  # becaues of /IMPLIB option when linking the executable. Unfortunately, there is no documented
  # way to disable the latter in CMake. So, moving the library to the bin directory (right next to the exe)
  set_target_properties(surelog-bin PROPERTIES ARCHIVE_OUTPUT_DIRECTORY ${CMAKE_CURRENT_BINARY_DIR}/bin)
  set_target_properties(hellouhdm PROPERTIES ARCHIVE_OUTPUT_DIRECTORY ${CMAKE_CURRENT_BINARY_DIR}/bin)
  set_target_properties(hellosureworld PROPERTIES ARCHIVE_OUTPUT_DIRECTORY ${CMAKE_CURRENT_BINARY_DIR}/bin)
endif()

target_link_libraries(surelog-bin PUBLIC surelog)
target_link_libraries(surelog PUBLIC antlr4_static)
target_link_libraries(surelog PUBLIC flatbuffers)
target_link_libraries(surelog PUBLIC uhdm)
add_dependencies(surelog flatc)
add_dependencies(GenerateSerializer uhdm)
add_dependencies(GenerateParser antlr4_static)
add_dependencies(surelog GenerateParser)
add_dependencies(surelog GenerateSerializer)

target_link_libraries(surelog PRIVATE ${Python3_LIBRARIES})
if($<BOOL:${TCMALLOC_LIBRARY}>)
  target_link_libraries(surelog PRIVATE tcmalloc)
endif()

if (UNIX)
  target_link_libraries(surelog PRIVATE stdc++fs)
  target_link_libraries(surelog PRIVATE dl)
  target_link_libraries(surelog PRIVATE util)
  target_link_libraries(surelog PRIVATE m)
  target_link_libraries(surelog PRIVATE rt)
  target_link_libraries(surelog PRIVATE pthread)
endif()

# Unit tests
enable_testing()
include(GoogleTest)
# All unit-tests are registered with this custom target as dependency, so
# just `make UnitTests` will build them all.
add_custom_target(UnitTests)

# Concise way to register a new google test
# call with register_gtest(path/to/UnitTestFile.cpp)
function(register_gtests)
  foreach(gtest_cc_file IN LISTS ARGN)
    # We create the binary name and test prefix from the cpp-filepath
    get_filename_component(test_bin ${gtest_cc_file} NAME_WE)
    get_filename_component(test_prefix ${gtest_cc_file} DIRECTORY)

    # Build binary, link all relevant libs and extract tests
    add_executable(${test_bin} EXCLUDE_FROM_ALL ${gtest_cc_file})

    # For simplicity, we link the test with libsurelog, but there is of
    # course a lot unnecessary churn if headers are modified.
    # Often it is sufficient to just have a few depeendencies.
    target_link_libraries(${test_bin} surelog gtest gmock gtest_main)
    gtest_discover_tests(${test_bin} TEST_PREFIX "${test_prefix}/")

    # Now, add this binary to our UnitTests target that it builds this
    add_dependencies(UnitTests ${test_bin})
  endforeach()
endfunction()

register_gtests(
  src/Utils/StringUtils_test.cpp
  src/DesignCompile/CompileHelper_test.cpp
  src/SourceCompile/SymbolTable_test.cpp
)

target_link_libraries(hellosureworld surelog)
target_link_libraries(hellouhdm surelog)

# Creation of the distribution directory, Precompiled package creation
add_custom_command(
  TARGET surelog-bin
  POST_BUILD
  COMMAND echo "       Creating platform independent staging for precompiled packages"
  COMMAND ${CMAKE_COMMAND} -E make_directory ${CMAKE_RUNTIME_OUTPUT_DIRECTORY}/sv
  COMMAND ${CMAKE_COMMAND} -E make_directory ${CMAKE_RUNTIME_OUTPUT_DIRECTORY}/python
  COMMAND ${CMAKE_COMMAND} -E remove_directory ${CMAKE_RUNTIME_OUTPUT_DIRECTORY}/slpp_all
  COMMAND ${CMAKE_COMMAND} -E remove_directory ${CMAKE_RUNTIME_OUTPUT_DIRECTORY}/slpp_unit
  COMMAND ${CMAKE_COMMAND} -E copy_if_different ${PROJECT_SOURCE_DIR}/src/API/builtin.sv
          ${CMAKE_RUNTIME_OUTPUT_DIRECTORY}/sv/builtin.sv
  COMMAND ${CMAKE_COMMAND} -E copy_if_different ${PROJECT_SOURCE_DIR}/src/API/slSV3_1aPythonListener.py
          ${CMAKE_RUNTIME_OUTPUT_DIRECTORY}/python/slSV3_1aPythonListener.py
  COMMAND ${CMAKE_COMMAND} -E copy_if_different ${PROJECT_SOURCE_DIR}/src/API/slformatmsg.py
          ${CMAKE_RUNTIME_OUTPUT_DIRECTORY}/python/slformatmsg.py
  COMMAND ${CMAKE_COMMAND} -E copy_if_different ${PROJECT_SOURCE_DIR}/src/API/slwaivers.py
          ${CMAKE_RUNTIME_OUTPUT_DIRECTORY}/python/slwaivers.py
  COMMAND echo "       Platform independent staging completed"
  WORKING_DIRECTORY "${CMAKE_RUNTIME_OUTPUT_DIRECTORY}")

if (WIN32)
  add_custom_command(
    TARGET surelog-bin
    POST_BUILD
    COMMAND echo "       Creating platform depdendent 'WIN32' staging for precompiled packages"
    COMMAND ${CMAKE_COMMAND} -E copy_directory ${PROJECT_SOURCE_DIR}/third_party/UVM/ovm-2.1.2 ovm-2.1.2
    COMMAND ${CMAKE_COMMAND} -E copy_directory ${PROJECT_SOURCE_DIR}/third_party/UVM/1800.2-2017-1.0 1800.2-2017-1.0
    COMMAND ${CMAKE_COMMAND} -E copy_directory ${PROJECT_SOURCE_DIR}/third_party/UVM/vmm-1.1.1a vmm-1.1.1a
    COMMAND ${CMAKE_COMMAND} -E copy_if_different
            ${Python3_RUNTIME_LIBRARY_DIRS}/python3${Python3_VERSION_MINOR}$<$<CONFIG:Debug>:_d>.dll
            ${CMAKE_RUNTIME_OUTPUT_DIRECTORY}
    COMMAND echo "       Platform depdendent staging completed"
    WORKING_DIRECTORY "${CMAKE_RUNTIME_OUTPUT_DIRECTORY}")
else()
  add_custom_command(
    TARGET surelog-bin
    POST_BUILD
    COMMAND echo "       Creating platform depdendent 'non-WIN32' staging for precompiled packages"
    COMMAND ln -fs ${PROJECT_SOURCE_DIR}/third_party/UVM/ovm-2.1.2
    COMMAND ln -fs ${PROJECT_SOURCE_DIR}/third_party/UVM/1800.2-2017-1.0
    COMMAND ln -fs ${PROJECT_SOURCE_DIR}/third_party/UVM/vmm-1.1.1a
    COMMAND echo "       Platform depdendent staging completed"
    WORKING_DIRECTORY "${CMAKE_RUNTIME_OUTPUT_DIRECTORY}")
endif()

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
  TARGETS antlr4_static flatbuffers
  ARCHIVE DESTINATION ${CMAKE_INSTALL_LIBDIR}/surelog)
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
        ${PROJECT_SOURCE_DIR}/src/Design/ParamAssign.h
        ${PROJECT_SOURCE_DIR}/src/Design/TfPortItem.h
        ${PROJECT_SOURCE_DIR}/src/Design/DesignElement.h
        ${PROJECT_SOURCE_DIR}/src/Design/Netlist.h
        ${PROJECT_SOURCE_DIR}/src/Design/Function.h
        ${PROJECT_SOURCE_DIR}/src/Design/Scope.h
        ${PROJECT_SOURCE_DIR}/src/Design/TimeInfo.h
        ${PROJECT_SOURCE_DIR}/src/Design/ModPort.h
        ${PROJECT_SOURCE_DIR}/src/Design/Union.h
        ${PROJECT_SOURCE_DIR}/src/Design/SimpleType.h
	${PROJECT_SOURCE_DIR}/src/Design/DummyType.h
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
        ${PROJECT_SOURCE_DIR}/src/Expression/Value.h
  DESTINATION ${CMAKE_INSTALL_INCLUDEDIR}/surelog/Expression)

if (WIN32 AND $<CONFIG:Debug>)
  install(
    FILES $<TARGET_PDB_FILE:surelog-bin>
          ${Python3_RUNTIME_LIBRARY_DIRS}/python${Python3_VERSION_MAJOR}${Python3_VERSION_MINOR}$<$<CONFIG:Debug>:_d>.dll
    DESTINATION ${CMAKE_INSTALL_BINDIR})
  install(
    FILES ${CMAKE_CURRENT_BINARY_DIR}/CMakeFiles/surelog.dir/surelog.pdb
          ${FlatBuffers_BINARY_DIR}/CMakeFiles/flatbuffers.dir/flatbuffers.pdb
          ${LIBANTLR4_BINARY_DIR}/runtime/CMakeFiles/antlr4_static.dir/antlr4_static.pdb
    DESTINATION ${CMAKE_INSTALL_LIBDIR}/surelog)
  install(
    FILES ${UHDM_BINARY_DIR}/CMakeFiles/uhdm.dir/uhdm.pdb
          ${UHDM_BINARY_DIR}/third_party/capnproto/c++/src/capnp/CMakeFiles/capnp.dir/capnp.pdb
          ${UHDM_BINARY_DIR}/third_party/capnproto/c++/src/kj/CMakeFiles/kj.dir/kj.pdb
    DESTINATION ${CMAKE_INSTALL_LIBDIR}/uhdm)
endif()
