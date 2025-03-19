find_package(Java QUIET COMPONENTS Runtime)

# Find ANTLR (antlr-runtime/include, libantlr-runtime.a, antlr.jar)
# This module defines:
# ANTLR_JAR_LOCATION, directory containing jar
# ANTLR_INCLUDE_DIR, directory containing headers
# ANTLR_LIBRARY, path to static library
#
# this might fail
# https://gitlab.kitware.com/cmake/cmake/issues/19120

# ANTLR JAR HANDLING
if(NOT ANTLR_JAR_LOCATION)
  find_file(ANTLR_JAR_LOCATION
            NAMES antlr-4.12.0-complete.jar antlr-4.13.0-complete.jar antlr-4.13.1-complete.jar antlr-4.13.2-complete.jar antlr.jar antlr4.jar antlr-4.jar
            HINTS /usr /usr/local /usr/local/share /usr/local/share/java /usr/local/lib/ /usr/share /usr/share/java /usr/local/Homebrew ~/homebrew /usr/local/homebrew/Cellar /opt/homebrew/Cellar
            PATH_SUFFIXES antlr 4.12.0 4.13.0 4.13.1 4.13.2 antlr/4.12.0 antlr/4.13.0 antlr/4.13.1 antlr/4.13.2
            NO_CMAKE_SYSTEM_PATH
            NO_SYSTEM_ENVIRONMENT_PATH)
    message("ANTLR Jar: ${ANTLR_JAR_LOCATION}")
endif()

if(ANTLR_JAR_LOCATION AND Java_JAVA_EXECUTABLE)
  execute_process(
      COMMAND ${Java_JAVA_EXECUTABLE} -jar ${ANTLR_JAR_LOCATION}
      OUTPUT_VARIABLE ANTLR_COMMAND_OUTPUT
      ERROR_VARIABLE ANTLR_COMMAND_ERROR
      RESULT_VARIABLE ANTLR_COMMAND_RESULT
      OUTPUT_STRIP_TRAILING_WHITESPACE)

  if(ANTLR_COMMAND_RESULT EQUAL 0)
    string(REGEX MATCH "Version [0-9]+(\\.[0-9]+)*" ANTLR_VERSION ${ANTLR_COMMAND_OUTPUT})
    string(REPLACE "Version " "" ANTLR_VERSION ${ANTLR_VERSION})
  else()
    message(
        SEND_ERROR
        "Command '${Java_JAVA_EXECUTABLE} -jar ${ANTLR_JAR_LOCATION}' "
        "failed with the output '${ANTLR_COMMAND_ERROR}'")
  endif()

  macro(ANTLR_TARGET Name InputFile)
    set(ANTLR_OPTIONS LEXER PARSER LISTENER VISITOR)
    set(ANTLR_ONE_VALUE_ARGS PACKAGE OUTPUT_DIRECTORY DEPENDS_ANTLR)
    set(ANTLR_MULTI_VALUE_ARGS COMPILE_FLAGS DEPENDS)
    cmake_parse_arguments(ANTLR_TARGET
                          "${ANTLR_OPTIONS}"
                          "${ANTLR_ONE_VALUE_ARGS}"
                          "${ANTLR_MULTI_VALUE_ARGS}"
                          ${ARGN})

    set(ANTLR_${Name}_INPUT ${InputFile})

    get_filename_component(ANTLR_INPUT ${InputFile} NAME_WE)

    if(ANTLR_TARGET_OUTPUT_DIRECTORY)
      set(ANTLR_${Name}_OUTPUT_DIR ${ANTLR_TARGET_OUTPUT_DIRECTORY})
    else()
      set(ANTLR_${Name}_OUTPUT_DIR
          ${CMAKE_CURRENT_BINARY_DIR}/antlr4cpp_generated_src/${ANTLR_INPUT})
    endif()

    unset(ANTLR_${Name}_CXX_OUTPUTS)

    if((ANTLR_TARGET_LEXER AND NOT ANTLR_TARGET_PARSER) OR
       (ANTLR_TARGET_PARSER AND NOT ANTLR_TARGET_LEXER))
      list(APPEND ANTLR_${Name}_CXX_OUTPUTS
           ${ANTLR_${Name}_OUTPUT_DIR}/${ANTLR_INPUT}.h
           ${ANTLR_${Name}_OUTPUT_DIR}/${ANTLR_INPUT}.cpp)
      set(ANTLR_${Name}_OUTPUTS
          ${ANTLR_${Name}_OUTPUT_DIR}/${ANTLR_INPUT}.interp
          ${ANTLR_${Name}_OUTPUT_DIR}/${ANTLR_INPUT}.tokens)
    else()
      list(APPEND ANTLR_${Name}_CXX_OUTPUTS
           ${ANTLR_${Name}_OUTPUT_DIR}/${ANTLR_INPUT}Lexer.h
           ${ANTLR_${Name}_OUTPUT_DIR}/${ANTLR_INPUT}Lexer.cpp
           ${ANTLR_${Name}_OUTPUT_DIR}/${ANTLR_INPUT}Parser.h
           ${ANTLR_${Name}_OUTPUT_DIR}/${ANTLR_INPUT}Parser.cpp)
      list(APPEND ANTLR_${Name}_OUTPUTS
           ${ANTLR_${Name}_OUTPUT_DIR}/${ANTLR_INPUT}Lexer.interp
           ${ANTLR_${Name}_OUTPUT_DIR}/${ANTLR_INPUT}Lexer.tokens)
    endif()

    if(ANTLR_TARGET_LISTENER)
      list(APPEND ANTLR_${Name}_CXX_OUTPUTS
           ${ANTLR_${Name}_OUTPUT_DIR}/${ANTLR_INPUT}BaseListener.h
           ${ANTLR_${Name}_OUTPUT_DIR}/${ANTLR_INPUT}BaseListener.cpp
           ${ANTLR_${Name}_OUTPUT_DIR}/${ANTLR_INPUT}Listener.h
           ${ANTLR_${Name}_OUTPUT_DIR}/${ANTLR_INPUT}Listener.cpp)
      list(APPEND ANTLR_TARGET_COMPILE_FLAGS -listener)
    endif()

    if(ANTLR_TARGET_VISITOR)
      list(APPEND ANTLR_${Name}_CXX_OUTPUTS
           ${ANTLR_${Name}_OUTPUT_DIR}/${ANTLR_INPUT}BaseVisitor.h
           ${ANTLR_${Name}_OUTPUT_DIR}/${ANTLR_INPUT}BaseVisitor.cpp
           ${ANTLR_${Name}_OUTPUT_DIR}/${ANTLR_INPUT}Visitor.h
           ${ANTLR_${Name}_OUTPUT_DIR}/${ANTLR_INPUT}Visitor.cpp)
      list(APPEND ANTLR_TARGET_COMPILE_FLAGS -visitor)
    endif()

    if(ANTLR_TARGET_PACKAGE)
      list(APPEND ANTLR_TARGET_COMPILE_FLAGS -package ${ANTLR_TARGET_PACKAGE})
    endif()

    list(APPEND ANTLR_${Name}_OUTPUTS ${ANTLR_${Name}_CXX_OUTPUTS})

    if(ANTLR_TARGET_DEPENDS_ANTLR)
      if(ANTLR_${ANTLR_TARGET_DEPENDS_ANTLR}_INPUT)
        list(APPEND ANTLR_TARGET_DEPENDS
             ${ANTLR_${ANTLR_TARGET_DEPENDS_ANTLR}_INPUT})
        list(APPEND ANTLR_TARGET_DEPENDS
             ${ANTLR_${ANTLR_TARGET_DEPENDS_ANTLR}_OUTPUTS})
      else()
        message(SEND_ERROR
                "ANTLR target '${ANTLR_TARGET_DEPENDS_ANTLR}' not found")
      endif()
    endif()

    add_custom_command(
        OUTPUT ${ANTLR_${Name}_OUTPUTS}
        COMMAND ${Java_JAVA_EXECUTABLE} -jar ${ANTLR_JAR_LOCATION}
                ${InputFile}
                -o ${ANTLR_${Name}_OUTPUT_DIR}
                -no-listener
                -Dlanguage=Cpp
                ${ANTLR_TARGET_COMPILE_FLAGS}
        DEPENDS ${InputFile}
                ${ANTLR_TARGET_DEPENDS}
        WORKING_DIRECTORY ${CMAKE_CURRENT_SOURCE_DIR}
        COMMENT "Building ${Name} with ANTLR ${ANTLR_VERSION}")
  endmacro(ANTLR_TARGET)

endif(ANTLR_JAR_LOCATION AND Java_JAVA_EXECUTABLE)

# ANTLR INCLUDE AND LIB
find_path(ANTLR_INCLUDE_DIR antlr4-runtime.h
  PATHS ${ANTLR_ROOT}/include
  HINTS /usr /usr/include /usr/local /usr/local/include /usr/local/Homebrew /usr/local/Homebrew/include  ~/homebrew ~/homebrew/include /opt/homebrew /opt/homebrew/include
  PATH_SUFFIXES antlr-runtime antlr4-runtime
  NO_CMAKE_SYSTEM_PATH
  NO_SYSTEM_ENVIRONMENT_PATH)

find_path(ANTLR_LIB_DIR
  NAMES libantlr4-runtime.a libantlr-runtime.a antlr_static.a antlr-static.a libantlr4-runtimeo.so libantlr-runtime.so antlr4.so antlr.so libantlr4-runtime.dylib libantlr-runtime.dylb antlr4.dylib antlr.dylib
  PATHS ${ANTLR_ROOT}/lib
  HINTS /usr /usr/local /usr/local/Homebrew ~/homebrew/ /opt/homebrew/
  PATH_SUFFIXES lib antlr-runtime antlr-runtime/lib lib/antlr-runtime
  NO_CMAKE_SYSTEM_PATH
  NO_SYSTEM_ENVIRONMENT_PATH)

if(BUILD_SHARED_LIBS)
  find_file(ANTLR_LIBRARY
    NAMES libantlr4-runtime.so libantlr-runtime.so antlr4.so antlr.so libantlr4-runtime.dylib libantlr-runtime.dylb antlr4.dylib antlr.dylib
    PATHS ${ANTLR_LIB_DIR}
    HINTS /usr /usr/local /usr/share /user/share/java /usr/local/Homebrew ~/homebrew/ /opt/homebrew/
    PATH_SUFFIXES lib antlr-runtime antlr-runtime/lib lib/antlr-runtime
    NO_CMAKE_SYSTEM_PATH
    NO_SYSTEM_ENVIRONMENT_PATH)
else()
  find_file(ANTLR_LIBRARY
    NAMES libantlr4-runtime.a libantlr-runtime.a antlr_static.a antlr-static.a
    PATHS ${ANTLR_LIB_DIR}
    HINTS /usr /usr/local /usr/share /usr/share/java /usr/local/Homebrew ~/homebrew/ /opt/homebrew/
    PATH_SUFFIXES lib antlr-runtime antlr-runtime/lib lib/antlr-runtime
    NO_CMAKE_SYSTEM_PATH
    NO_SYSTEM_ENVIRONMENT_PATH)
endif()

include(FindPackageHandleStandardArgs)
find_package_handle_standard_args(
    ANTLR
    REQUIRED_VARS ANTLR_JAR_LOCATION Java_JAVA_EXECUTABLE ANTLR_INCLUDE_DIR ANTLR_LIBRARY
    VERSION_VAR ANTLR_VERSION)
