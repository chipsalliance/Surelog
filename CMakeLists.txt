# -*- mode:cmake -*-
cmake_minimum_required(VERSION 3.15 FATAL_ERROR)

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

set(CMAKE_CXX_STANDARD 17)
set(CMAKE_CXX_STANDARD_REQUIRED ON)
set(CMAKE_EXPORT_COMPILE_COMMANDS ON)

set(FLATBUFFERS_BUILD_TESTS OFF CACHE BOOL "Skip flatbuffers' tests")
add_subdirectory(third_party/flatbuffers EXCLUDE_FROM_ALL)
add_subdirectory(third_party/antlr4_fast/runtime/Cpp EXCLUDE_FROM_ALL)

set(UHDM_BUILD_TESTS OFF CACHE BOOL "Skip UHDM tests")
add_subdirectory(third_party/UHDM)
add_subdirectory(third_party/googletest EXCLUDE_FROM_ALL)

# NOTE: Set the global output directories after the subprojects have had their go at it
set(CMAKE_ARCHIVE_OUTPUT_DIRECTORY ${CMAKE_CURRENT_BINARY_DIR}/lib)
set(CMAKE_LIBRARY_OUTPUT_DIRECTORY ${CMAKE_CURRENT_BINARY_DIR}/bin)
set(CMAKE_RUNTIME_OUTPUT_DIRECTORY ${CMAKE_CURRENT_BINARY_DIR}/bin)

set(GENDIR ${CMAKE_CURRENT_BINARY_DIR}/generated)

# Python
if (SURELOG_WITH_PYTHON)
  find_package(Python3 3.3 REQUIRED COMPONENTS Interpreter Development)
  find_package(SWIG 3.0 REQUIRED)
  message(STATUS "Python3_LIBRARIES = ${Python3_LIBRARIES}")
  message(STATUS "Python3_EXECUTABLE = ${Python3_EXECUTABLE}")
  message(STATUS "Python3_INCLUDE_DIRS = ${Python3_INCLUDE_DIRS}")
  message(STATUS "Python3_RUNTIME_LIBRARY_DIRS = ${Python3_RUNTIME_LIBRARY_DIRS}")
else()
  find_package(Python3 3.3 REQUIRED Interpreter)
  message(STATUS "Python3_EXECUTABLE = ${Python3_EXECUTABLE}")
endif()

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
  #set(MEM_SANITIZER_FLAGS
  #    "-fsanitize=address -fno-omit-frame-pointer"
  #)
  set(CMAKE_CXX_FLAGS_DEBUG
      "${CMAKE_CXX_FLAGS_DEBUG} ${TCMALLOC_COMPILE_OPTIONS} -Wall -O0 -g ${MSYS_COMPILE_OPTIONS} ${MY_CXX_WARNING_FLAGS} ${MEM_SANITIZER_FLAGS}"
  )
  set(CMAKE_CXX_FLAGS_RELEASE
      "${CMAKE_CXX_FLAGS_RELEASE} ${TCMALLOC_COMPILE_OPTIONS} -Wall -O3 ${MSYS_COMPILE_OPTIONS} -DNDEBUG ${MY_CXX_WARNING_FLAGS}"
  )
endif()

# Flatbuffer
set(flatbuffer-GENERATED_SRC
    ${GENDIR}/include/Surelog/Cache/header_generated.h
    ${GENDIR}/include/Surelog/Cache/parser_generated.h
    ${GENDIR}/include/Surelog/Cache/preproc_generated.h
    ${GENDIR}/include/Surelog/Cache/python_api_generated.h)

foreach(header_file ${flatbuffer-GENERATED_SRC})
  set_source_files_properties(${header_file} PROPERTIES GENERATED TRUE)
endforeach(header_file ${flatbuffer-GENERATED_SRC})
add_custom_target(GenerateSerializer DEPENDS ${flatbuffer-GENERATED_SRC})
add_custom_command(
  OUTPUT ${flatbuffer-GENERATED_SRC}
  COMMAND
    flatc --cpp --binary -o ${GENDIR}/include/Surelog/Cache
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
    ${PROJECT_SOURCE_DIR}/third_party/antlr4_fast/antlr4-4.9.3-complete.jar)

add_custom_target(GenerateParser DEPENDS
  ${GENDIR}/src/parser/generated-parsers.tstamp
  ${GENDIR}/src/SourceCompile/VObjectTypes.cpp)

set(surelog_grammars
  ${PROJECT_SOURCE_DIR}/grammar/SV3_1aLexer.g4
  ${PROJECT_SOURCE_DIR}/grammar/SV3_1aParser.g4
  ${PROJECT_SOURCE_DIR}/grammar/SV3_1aPpLexer.g4
  ${PROJECT_SOURCE_DIR}/grammar/SV3_1aPpParser.g4
  ${PROJECT_SOURCE_DIR}/grammar/SV3_1aSplitterLexer.g4
  ${PROJECT_SOURCE_DIR}/grammar/SV3_1aSplitterParser.g4
)

set(surelog_grammars-GENERATED_SRC
  ${GENDIR}/src/parser/SV3_1aLexer.h
  ${GENDIR}/src/parser/SV3_1aParserBaseListener.h
  ${GENDIR}/src/parser/SV3_1aParser.h
  ${GENDIR}/src/parser/SV3_1aParserListener.h
  ${GENDIR}/src/parser/SV3_1aLexer.cpp
  ${GENDIR}/src/parser/SV3_1aParserBaseListener.cpp
  ${GENDIR}/src/parser/SV3_1aParser.cpp
  ${GENDIR}/src/parser/SV3_1aParserListener.cpp

  ${GENDIR}/src/parser/SV3_1aPpLexer.h
  ${GENDIR}/src/parser/SV3_1aPpParserBaseListener.h
  ${GENDIR}/src/parser/SV3_1aPpParser.h
  ${GENDIR}/src/parser/SV3_1aPpParserListener.h
  ${GENDIR}/src/parser/SV3_1aPpLexer.cpp
  ${GENDIR}/src/parser/SV3_1aPpParserBaseListener.cpp
  ${GENDIR}/src/parser/SV3_1aPpParser.cpp
  ${GENDIR}/src/parser/SV3_1aPpParserListener.cpp
)

add_custom_command(
  OUTPUT ${surelog_grammars-GENERATED_SRC} ${GENDIR}/src/parser/generated-parsers.tstamp
  WORKING_DIRECTORY "${PROJECT_SOURCE_DIR}/grammar/"
  COMMAND echo "---------- Parser generation..."
  COMMAND ${CMAKE_COMMAND} -E make_directory ${GENDIR}/src/parser/
  # We can't use ${surelog_grammars} here, as then the generated files would
  # contain a reference to the full path-name (issue #88).
  # Unfortunately, cmake does not provide simple equivalents to
  # gmake's $(nodir $(surelog_grammars)).
  # So, we list them here all manually passing to the command.
  COMMAND java -jar ${ANTLR_JAR_LOCATION} -Werror -Dlanguage=Cpp -package SURELOG
             -o ${GENDIR}/src/parser/
             SV3_1aLexer.g4    SV3_1aParser.g4
             SV3_1aPpLexer.g4  SV3_1aPpParser.g4
  DEPENDS ${ANTLR_JAR_LOCATION} ${surelog_grammars}
  COMMAND ${CMAKE_COMMAND} -E touch ${GENDIR}/src/parser/generated-parsers.tstamp
)

add_custom_command(
  OUTPUT ${GENDIR}/include/Surelog/SourceCompile/VObjectTypes.h
         ${GENDIR}/include/Surelog/API/VObjectTypes_py.h
         ${GENDIR}/include/Surelog/SourceCompile/SV3_1aTreeShapeListener.h
         ${GENDIR}/include/Surelog/SourceCompile/SV3_1aPpTreeShapeListener.h
         ${GENDIR}/src/SourceCompile/VObjectTypes.cpp
  DEPENDS ${GENDIR}/src/parser/generated-parsers.tstamp
          ${GENDIR}/src/parser/SV3_1aParserBaseListener.h
          ${GENDIR}/src/parser/SV3_1aPpParserBaseListener.h
          ${PROJECT_SOURCE_DIR}/scripts/generate_parser_listener.py
          ${PROJECT_SOURCE_DIR}/src/SourceCompile/SV3_1aTreeShapeListener.cpp
          ${PROJECT_SOURCE_DIR}/src/SourceCompile/SV3_1aPpTreeShapeListener.cpp

  WORKING_DIRECTORY ${PROJECT_SOURCE_DIR}
  COMMAND echo "---------- VObjectTypes, Listener generation"
  COMMAND ${Python3_EXECUTABLE} scripts/generate_parser_listener.py --input-dirpath ${PROJECT_SOURCE_DIR} --output-dirpath ${GENDIR}
)

if (SURELOG_WITH_PYTHON)
  set(surelog_python-GENERATED_SRC
    ${GENDIR}/include/Surelog/API/SV3_1aPythonListener.h
    ${GENDIR}/include/Surelog/API/slapi_scripts.h
    ${GENDIR}/include/Surelog/API/slapi_wrap.cxx
    ${GENDIR}/include/Surelog/API/slapi.py
    ${GENDIR}/src/API/slSV3_1aPythonListener.py)
  foreach(gen_src ${surelog_python-GENERATED_SRC})
    set_source_files_properties(${gen_src} PROPERTIES GENERATED TRUE)
  endforeach()
  add_custom_command(
    OUTPUT  ${surelog_python-GENERATED_SRC}
    DEPENDS ${GENDIR}/include/Surelog/API/VObjectTypes_py.h
            ${PROJECT_SOURCE_DIR}/src/API/slapi_scripts.i
            ${PROJECT_SOURCE_DIR}/scripts/generate_python_listener.py
            ${PROJECT_SOURCE_DIR}/scripts/embed_python_api.py
            ${GENDIR}/src/parser/generated-parsers.tstamp

    WORKING_DIRECTORY "${PROJECT_SOURCE_DIR}"
    COMMAND echo "---------- Python API generation"
    COMMAND ${Python3_EXECUTABLE} scripts/generate_python_listener.py
            --template-header-filepath ${GENDIR}/src/parser/SV3_1aParserBaseListener.h
            --output-dirpath ${GENDIR}
    COMMAND ${SWIG_EXECUTABLE} -c++ -python
            -I${PROJECT_SOURCE_DIR}/include
            -o ${GENDIR}/include/Surelog/API/slapi_wrap.cxx
            ${PROJECT_SOURCE_DIR}/src/API/slapi_scripts.i
    COMMAND ${Python3_EXECUTABLE} scripts/embed_python_api.py
            --template-script-filepaths ${GENDIR}/include/Surelog/API/slapi.py ${PROJECT_SOURCE_DIR}/src/API/slformatmsg.py
            --output-dirpath ${GENDIR}/include/Surelog/API
  )
endif()

include_directories(${PROJECT_SOURCE_DIR}/include ${GENDIR}/include ${GENDIR}/src)

# Put source code here, files that are generated at build time in
# surelog_generated_SRC
set(surelog_SRC
  ${PROJECT_SOURCE_DIR}/src/API/Surelog.cpp
  ${PROJECT_SOURCE_DIR}/src/API/SLAPI.cpp
  ${PROJECT_SOURCE_DIR}/src/API/PythonAPI.cpp
  ${PROJECT_SOURCE_DIR}/src/Cache/Cache.cpp
  ${PROJECT_SOURCE_DIR}/src/Cache/PPCache.cpp
  ${PROJECT_SOURCE_DIR}/src/Cache/ParseCache.cpp
  ${PROJECT_SOURCE_DIR}/src/CommandLine/CommandLineParser.cpp
  ${PROJECT_SOURCE_DIR}/src/Common/ClockingBlockHolder.cpp
  ${PROJECT_SOURCE_DIR}/src/Config/Config.cpp
  ${PROJECT_SOURCE_DIR}/src/Config/ConfigSet.cpp
  ${PROJECT_SOURCE_DIR}/src/Design/DataType.cpp
  ${PROJECT_SOURCE_DIR}/src/Design/DefParam.cpp
  ${PROJECT_SOURCE_DIR}/src/Design/Design.cpp
  ${PROJECT_SOURCE_DIR}/src/Design/BindStmt.cpp
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
  ${PROJECT_SOURCE_DIR}/src/DesignCompile/CompilerHarness.cpp
  ${PROJECT_SOURCE_DIR}/src/DesignCompile/CompileExpression.cpp
  ${PROJECT_SOURCE_DIR}/src/DesignCompile/CompileFileContent.cpp
  ${PROJECT_SOURCE_DIR}/src/DesignCompile/CompileHelper.cpp
  ${PROJECT_SOURCE_DIR}/src/DesignCompile/EvalFunc.cpp
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
  ${PROJECT_SOURCE_DIR}/src/DesignCompile/ElaboratorHarness.cpp
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
  ${PROJECT_SOURCE_DIR}/src/ErrorReporting/LogListener.cpp
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
  ${PROJECT_SOURCE_DIR}/src/SourceCompile/ParserHarness.cpp
  ${PROJECT_SOURCE_DIR}/src/SourceCompile/PreprocessFile.cpp
  ${PROJECT_SOURCE_DIR}/src/SourceCompile/PreprocessHarness.cpp
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

if (SURELOG_WITH_PYTHON)
  list(APPEND surelog_SRC
    ${GENDIR}/include/Surelog/API/SV3_1aPythonListener.h
    ${PROJECT_SOURCE_DIR}/src/API/SV3_1aPythonListener.cpp
    ${PROJECT_SOURCE_DIR}/src/SourceCompile/PythonListen.cpp
    ${PROJECT_SOURCE_DIR}/src/Cache/PythonAPICache.cpp
  )
endif()

set(surelog_generated_SRC
  # generated parser
  ${surelog_grammars-GENERATED_SRC}

  # Derived from parser generation.
  ${GENDIR}/src/SourceCompile/VObjectTypes.cpp)

foreach(gen_src ${surelog_generated_SRC})
  set_source_files_properties(${gen_src} PROPERTIES GENERATED TRUE)
endforeach()

add_library(surelog STATIC ${surelog_SRC} ${surelog_generated_SRC})
set_target_properties(surelog PROPERTIES PUBLIC_HEADER include/Surelog/surelog.h)
target_include_directories(surelog PRIVATE
  third_party/antlr4_fast/runtime/Cpp/runtime/src
  third_party/flatbuffers/include
  third_party/googletest/googletest/include
  third_party/googletest/googlemock/include)
target_include_directories(surelog PUBLIC $<INSTALL_INTERFACE:include>)
if (SURELOG_WITH_PYTHON)
  target_include_directories(surelog PUBLIC ${Python3_INCLUDE_DIRS}) # Keep this at the end
  target_compile_definitions(surelog PUBLIC SURELOG_WITH_PYTHON)
endif()
add_executable(surelog-bin ${PROJECT_SOURCE_DIR}/src/main.cpp)
set_target_properties(surelog-bin PROPERTIES OUTPUT_NAME surelog)

if (APPLE)
  # In macOS, it is necessary to add the correct @rpath to the executable for
  # finding python dynamic libraries ref: https://gitlab.kitware.com/cmake/cmake/-/issues/21293
  # https://gitlab.kitware.com/cmake/cmake/-/issues/21947
  # Python3_LINK_OPTIONS is variable available from cmake 3.19, update cmake using homebrew
  # if can't update cmake use:
  # set_target_properties(surelog-bin PROPERTIES BUILD_WITH_INSTALL_RPATH TRUE
  # INSTALL_RPATH "/Library/Developer/CommandLineTools/Library/Frameworks/")
  # if you installed python with hombrew. Or if you install python with Xcode:
  # set_target_properties(surelog-bin PROPERTIES BUILD_WITH_INSTALL_RPATH TRUE
  # INSTALL_RPATH "/Applications/Xcode.app/Contents/Developer/Library/Frameworks/")
  if (SURELOG_WITH_PYTHON)
    target_link_options(surelog-bin PRIVATE ${Python3_LINK_OPTIONS})
  endif()
endif()

if (NOT QUICK_COMP)
add_executable(hellosureworld ${PROJECT_SOURCE_DIR}/src/hellosureworld.cpp)
add_executable(hellouhdm ${PROJECT_SOURCE_DIR}/src/hellouhdm.cpp)
add_executable(hellodesign ${PROJECT_SOURCE_DIR}/src/hellodesign.cpp)
endif()

if(MSVC OR WIN32)
  # We have two files named "surelog.lib" and both getting generated in the lib folder
  # One is the surelog.lib generated by the surelog target and the other is the one generated
  # becaues of /IMPLIB option when linking the executable. Unfortunately, there is no documented
  # way to disable the latter in CMake. So, moving the library to the bin directory (right next to the exe)
  set_target_properties(surelog-bin PROPERTIES ARCHIVE_OUTPUT_DIRECTORY ${CMAKE_CURRENT_BINARY_DIR}/bin)
  set_target_properties(hellouhdm PROPERTIES ARCHIVE_OUTPUT_DIRECTORY ${CMAKE_CURRENT_BINARY_DIR}/bin)
  set_target_properties(hellodesign PROPERTIES ARCHIVE_OUTPUT_DIRECTORY ${CMAKE_CURRENT_BINARY_DIR}/bin)
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

if (SURELOG_WITH_PYTHON)
  target_link_libraries(surelog PRIVATE ${Python3_LIBRARIES})
endif()

#NOT WORKING: if($<BOOL:${TCMALLOC_LIBRARY}>)
if(NOT NO_TCMALLOC)
  find_library(TCMALLOC_LIBRARY NAMES tcmalloc)
  if(TCMALLOC_LIBRARY)
    target_link_libraries(surelog PRIVATE tcmalloc)
  endif()
endif()

if (UNIX)
  target_link_libraries(surelog PRIVATE dl)
  target_link_libraries(surelog PRIVATE util)
  target_link_libraries(surelog PRIVATE m)
  target_link_libraries(surelog PRIVATE pthread)
endif()

if (CMAKE_SYSTEM_NAME MATCHES "Linux")
  target_link_libraries(uhdm PRIVATE stdc++fs)
  target_link_libraries(surelog PRIVATE stdc++fs)
  target_link_libraries(surelog PRIVATE rt)
endif()

# Unit tests
enable_testing()
include(GoogleTest)

if(MSVC)
  # Microsoft reports the value of __cplusplus wrong and gmock/gtest pulls in the
  # string_view implementation based on it's value. Microsoft's solution is to
  # provide additional flags to make the value correct. More info can be found here -
  #
  #   https://docs.microsoft.com/en-us/cpp/build/reference/zc-cplusplus?view=msvc-160
  #   https://devblogs.microsoft.com/cppblog/msvc-now-correctly-reports-__cplusplus/
  target_compile_options(gmock PRIVATE /Zc:__cplusplus)
  target_compile_options(gmock_main PRIVATE /Zc:__cplusplus)
  target_compile_options(gtest PRIVATE /Zc:__cplusplus)
  target_compile_options(gtest_main PRIVATE /Zc:__cplusplus)
endif()

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

    target_include_directories(${test_bin} PRIVATE
      ${PROJECT_SOURCE_DIR}/third_party/antlr4_fast/runtime/Cpp/runtime/src
      ${PROJECT_SOURCE_DIR}/third_party/flatbuffers/include)
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
  src/Utils/FileUtils_test.cpp
  src/SourceCompile/SymbolTable_test.cpp
  src/Expression/ExprBuilder_test.cpp
  src/SourceCompile/PreprocessFile_test.cpp
  src/SourceCompile/ParseFile_test.cpp
  src/DesignCompile/CompileExpression_test.cpp
  src/DesignCompile/Elaboration_test.cpp
  src/DesignCompile/Uhdm_test.cpp
)

if (NOT QUICK_COMP)
target_link_libraries(hellosureworld surelog)
target_link_libraries(hellouhdm surelog)
target_link_libraries(hellodesign surelog)
endif()

# Creation of the distribution directory, Precompiled package creation
add_custom_command(
  TARGET surelog-bin
  POST_BUILD
  COMMAND echo "       Creating platform independent staging for precompiled packages"
  COMMAND ${CMAKE_COMMAND} -E make_directory ${CMAKE_RUNTIME_OUTPUT_DIRECTORY}/python
  COMMAND ${CMAKE_COMMAND} -E remove_directory ${CMAKE_RUNTIME_OUTPUT_DIRECTORY}/slpp_all
  COMMAND ${CMAKE_COMMAND} -E remove_directory ${CMAKE_RUNTIME_OUTPUT_DIRECTORY}/slpp_unit
  COMMAND echo "       Platform independent staging completed"
  WORKING_DIRECTORY "${CMAKE_RUNTIME_OUTPUT_DIRECTORY}"
)

if (SURELOG_WITH_PYTHON)
  add_custom_command(
    TARGET surelog-bin
    POST_BUILD
    COMMAND ${CMAKE_COMMAND} -E copy_if_different ${GENDIR}/src/API/slSV3_1aPythonListener.py
            ${CMAKE_RUNTIME_OUTPUT_DIRECTORY}/python/slSV3_1aPythonListener.py
    COMMAND ${CMAKE_COMMAND} -E copy_if_different ${PROJECT_SOURCE_DIR}/src/API/slformatmsg.py
            ${CMAKE_RUNTIME_OUTPUT_DIRECTORY}/python/slformatmsg.py
    COMMAND ${CMAKE_COMMAND} -E copy_if_different ${PROJECT_SOURCE_DIR}/src/API/slwaivers.py
            ${CMAKE_RUNTIME_OUTPUT_DIRECTORY}/python/slwaivers.py
  )
endif()

if (WIN32)
  if (SURELOG_WITH_PYTHON)
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
      COMMAND echo "       Creating platform depdendent 'WIN32' staging for precompiled packages"
      COMMAND ${CMAKE_COMMAND} -E copy_directory ${PROJECT_SOURCE_DIR}/third_party/UVM/ovm-2.1.2 ovm-2.1.2
      COMMAND ${CMAKE_COMMAND} -E copy_directory ${PROJECT_SOURCE_DIR}/third_party/UVM/1800.2-2017-1.0 1800.2-2017-1.0
      COMMAND ${CMAKE_COMMAND} -E copy_directory ${PROJECT_SOURCE_DIR}/third_party/UVM/vmm-1.1.1a vmm-1.1.1a
      COMMAND echo "       Platform depdendent staging completed"
      WORKING_DIRECTORY "${CMAKE_RUNTIME_OUTPUT_DIRECTORY}")
  endif()
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
    -writepp -mt 0 -parse -nocomp -noelab -nostdout >> ovm_pkg.log
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
    -parse -nocomp -noelab -nostdout  >> uvm_pkg.log
  COMMAND echo "       Package UVM created"
  WORKING_DIRECTORY "${CMAKE_RUNTIME_OUTPUT_DIRECTORY}")

if (NOT QUICK_COMP)
add_dependencies(hellosureworld PrecompileOVM)
add_dependencies(hellosureworld PrecompileUVM)
endif()

# Installation target
install(
  TARGETS surelog-bin
  RUNTIME DESTINATION ${CMAKE_INSTALL_BINDIR})
install(
  TARGETS surelog antlr4_static flatbuffers
  EXPORT Surelog
  ARCHIVE DESTINATION ${CMAKE_INSTALL_LIBDIR}/surelog
  PUBLIC_HEADER DESTINATION ${CMAKE_INSTALL_INCLUDEDIR}/Surelog)
install(
  TARGETS uhdm capnp kj
  EXPORT Surelog
  ARCHIVE DESTINATION ${CMAKE_INSTALL_LIBDIR}/uhdm
  PUBLIC_HEADER DESTINATION ${CMAKE_INSTALL_INCLUDEDIR}/uhdm)

if (SURELOG_WITH_PYTHON)
  install(
    DIRECTORY ${CMAKE_RUNTIME_OUTPUT_DIRECTORY}/python
    DESTINATION ${CMAKE_INSTALL_LIBDIR}/surelog)
endif()

install(DIRECTORY ${CMAKE_RUNTIME_OUTPUT_DIRECTORY}/pkg
  DESTINATION ${CMAKE_INSTALL_LIBDIR}/surelog)
install(
  FILES ${PROJECT_SOURCE_DIR}/include/Surelog/CommandLine/CommandLineParser.h
  DESTINATION ${CMAKE_INSTALL_INCLUDEDIR}/Surelog/CommandLine)
install(
  FILES ${PROJECT_SOURCE_DIR}/include/Surelog/SourceCompile/SymbolTable.h
        ${GENDIR}/include/Surelog/SourceCompile/VObjectTypes.h
  DESTINATION ${CMAKE_INSTALL_INCLUDEDIR}/Surelog/SourceCompile)
install(
  FILES ${PROJECT_SOURCE_DIR}/include/Surelog/ErrorReporting/Location.h
        ${PROJECT_SOURCE_DIR}/include/Surelog/ErrorReporting/Error.h
        ${PROJECT_SOURCE_DIR}/include/Surelog/ErrorReporting/ErrorDefinition.h
        ${PROJECT_SOURCE_DIR}/include/Surelog/ErrorReporting/ErrorContainer.h
        ${PROJECT_SOURCE_DIR}/include/Surelog/ErrorReporting/LogListener.h
        ${PROJECT_SOURCE_DIR}/include/Surelog/ErrorReporting/Report.h
        ${PROJECT_SOURCE_DIR}/include/Surelog/ErrorReporting/Waiver.h
  DESTINATION ${CMAKE_INSTALL_INCLUDEDIR}/Surelog/ErrorReporting)
install(
  FILES ${PROJECT_SOURCE_DIR}/include/Surelog/API/PythonAPI.h
        ${PROJECT_SOURCE_DIR}/include/Surelog/API/SLAPI.h
        ${PROJECT_SOURCE_DIR}/include/Surelog/API/Surelog.h
  DESTINATION ${CMAKE_INSTALL_INCLUDEDIR}/Surelog/API)
install(
  FILES ${PROJECT_SOURCE_DIR}/include/Surelog/Common/ClockingBlockHolder.h
        ${PROJECT_SOURCE_DIR}/include/Surelog/Common/Containers.h
        ${PROJECT_SOURCE_DIR}/include/Surelog/Common/PortNetHolder.h
        ${PROJECT_SOURCE_DIR}/include/Surelog/Common/RTTI.h
        ${PROJECT_SOURCE_DIR}/include/Surelog/Common/SymbolId.h
  DESTINATION ${CMAKE_INSTALL_INCLUDEDIR}/Surelog/Common)
install(
  FILES ${PROJECT_SOURCE_DIR}/include/Surelog/DesignCompile/CompileHelper.h
  DESTINATION ${CMAKE_INSTALL_INCLUDEDIR}/Surelog/DesignCompile)
install(
  FILES ${PROJECT_SOURCE_DIR}/include/Surelog/Design/ClockingBlock.h
        ${PROJECT_SOURCE_DIR}/include/Surelog/Design/Design.h
        ${PROJECT_SOURCE_DIR}/include/Surelog/Design/BindStmt.h
        ${PROJECT_SOURCE_DIR}/include/Surelog/Design/Instance.h
        ${PROJECT_SOURCE_DIR}/include/Surelog/Design/Signal.h
        ${PROJECT_SOURCE_DIR}/include/Surelog/Design/ValuedComponentI.h
        ${PROJECT_SOURCE_DIR}/include/Surelog/Design/DataType.h
        ${PROJECT_SOURCE_DIR}/include/Surelog/Design/Enum.h
        ${PROJECT_SOURCE_DIR}/include/Surelog/Design/Struct.h
        ${PROJECT_SOURCE_DIR}/include/Surelog/Design/ModuleDefinition.h
        ${PROJECT_SOURCE_DIR}/include/Surelog/Design/Statement.h
        ${PROJECT_SOURCE_DIR}/include/Surelog/Design/VObject.h
        ${PROJECT_SOURCE_DIR}/include/Surelog/Design/DefParam.h
        ${PROJECT_SOURCE_DIR}/include/Surelog/Design/FileCNodeId.h
        ${PROJECT_SOURCE_DIR}/include/Surelog/Design/ModuleInstance.h
        ${PROJECT_SOURCE_DIR}/include/Surelog/Design/Task.h
        ${PROJECT_SOURCE_DIR}/include/Surelog/Design/DesignComponent.h
        ${PROJECT_SOURCE_DIR}/include/Surelog/Design/FileContent.h
        ${PROJECT_SOURCE_DIR}/include/Surelog/Design/Parameter.h
        ${PROJECT_SOURCE_DIR}/include/Surelog/Design/ParamAssign.h
        ${PROJECT_SOURCE_DIR}/include/Surelog/Design/TfPortItem.h
        ${PROJECT_SOURCE_DIR}/include/Surelog/Design/DesignElement.h
        ${PROJECT_SOURCE_DIR}/include/Surelog/Design/Netlist.h
        ${PROJECT_SOURCE_DIR}/include/Surelog/Design/Function.h
        ${PROJECT_SOURCE_DIR}/include/Surelog/Design/Scope.h
        ${PROJECT_SOURCE_DIR}/include/Surelog/Design/TimeInfo.h
        ${PROJECT_SOURCE_DIR}/include/Surelog/Design/ModPort.h
        ${PROJECT_SOURCE_DIR}/include/Surelog/Design/Union.h
        ${PROJECT_SOURCE_DIR}/include/Surelog/Design/SimpleType.h
        ${PROJECT_SOURCE_DIR}/include/Surelog/Design/DummyType.h
  DESTINATION ${CMAKE_INSTALL_INCLUDEDIR}/Surelog/Design)
install(
  FILES ${PROJECT_SOURCE_DIR}/include/Surelog/Testbench/ClassDefinition.h
        ${PROJECT_SOURCE_DIR}/include/Surelog/Testbench/CoverGroupDefinition.h
        ${PROJECT_SOURCE_DIR}/include/Surelog/Testbench/Property.h
        ${PROJECT_SOURCE_DIR}/include/Surelog/Testbench/Variable.h
        ${PROJECT_SOURCE_DIR}/include/Surelog/Testbench/ClassObject.h
        ${PROJECT_SOURCE_DIR}/include/Surelog/Testbench/FunctionMethod.h
        ${PROJECT_SOURCE_DIR}/include/Surelog/Testbench/TaskMethod.h
        ${PROJECT_SOURCE_DIR}/include/Surelog/Testbench/Constraint.h
        ${PROJECT_SOURCE_DIR}/include/Surelog/Testbench/Program.h
        ${PROJECT_SOURCE_DIR}/include/Surelog/Testbench/TypeDef.h
  DESTINATION ${CMAKE_INSTALL_INCLUDEDIR}/Surelog/Testbench)
install(
  FILES ${PROJECT_SOURCE_DIR}/include/Surelog/Package/Package.h
  DESTINATION ${CMAKE_INSTALL_INCLUDEDIR}/Surelog/Package)
install(
  FILES ${PROJECT_SOURCE_DIR}/include/Surelog/Library/Library.h
        ${PROJECT_SOURCE_DIR}/include/Surelog/Library/LibrarySet.h
  DESTINATION ${CMAKE_INSTALL_INCLUDEDIR}/Surelog/Library)
install(
  FILES ${PROJECT_SOURCE_DIR}/include/Surelog/Config/Config.h
        ${PROJECT_SOURCE_DIR}/include/Surelog/Config/ConfigSet.h
  DESTINATION ${CMAKE_INSTALL_INCLUDEDIR}/Surelog/Config)
install(
  FILES ${PROJECT_SOURCE_DIR}/include/Surelog/Expression/ExprBuilder.h
        ${PROJECT_SOURCE_DIR}/include/Surelog/Expression/Value.h
  DESTINATION ${CMAKE_INSTALL_INCLUDEDIR}/Surelog/Expression)

if (WIN32 AND $<CONFIG:Debug>)
  if (SURELOG_WITH_PYTHON)
    install(
      FILES $<TARGET_PDB_FILE:surelog-bin>
            ${Python3_RUNTIME_LIBRARY_DIRS}/python${Python3_VERSION_MAJOR}${Python3_VERSION_MINOR}$<$<CONFIG:Debug>:_d>.dll
      DESTINATION ${CMAKE_INSTALL_BINDIR})
  endif()
  install(
    FILES $<TARGET_PDB_FILE:surelog-bin>
          ${UHDM_BINARY_DIR}/bin/uhdm-dump.pdb
          ${UHDM_BINARY_DIR}/bin/uhdm-hier.pdb
    DESTINATION ${CMAKE_INSTALL_BINDIR})
  install(
    FILES ${CMAKE_CURRENT_BINARY_DIR}/CMakeFiles/surelog.dir/surelog.pdb
          ${FlatBuffers_BINARY_DIR}/CMakeFiles/flatbuffers.dir/flatbuffers.pdb
          ${LIBANTLR4_BINARY_DIR}/runtime/CMakeFiles/antlr4_static.dir/antlr4_static.pdb
    DESTINATION ${CMAKE_INSTALL_LIBDIR}/surelog)
  install(
    FILES ${UHDM_BINARY_DIR}/CMakeFiles/uhdm.dir/uhdm.pdb
          ${Cap\'n\ Proto_BINARY_DIR}/src/capnp/CMakeFiles/capnp.dir/capnp.pdb
          ${Cap\'n\ Proto_BINARY_DIR}/src/kj/CMakeFiles/kj.dir/kj.pdb
    DESTINATION ${CMAKE_INSTALL_LIBDIR}/uhdm)
endif()

install(
  EXPORT Surelog
  FILE Surelog.cmake
  DESTINATION cmake)
include(CMakePackageConfigHelpers)

# generate the config file that is includes the exports
configure_package_config_file(
  ${CMAKE_CURRENT_SOURCE_DIR}/Config.cmake.in
  "${CMAKE_CURRENT_BINARY_DIR}/SurelogConfig.cmake"
  INSTALL_DESTINATION cmake
  NO_SET_AND_CHECK_MACRO
  NO_CHECK_REQUIRED_COMPONENTS_MACRO)

# install the configuration file
install(
  FILES ${CMAKE_CURRENT_BINARY_DIR}/SurelogConfig.cmake
  DESTINATION cmake)

ADD_CUSTOM_TARGET(
  link_target ALL
  COMMAND ${CMAKE_COMMAND} -E create_symlink
  build/compile_commands.json ${PROJECT_SOURCE_DIR}/compile_commands.json)
