cmake_minimum_required(VERSION 3.7.2)

# Find UHDM (uhdm/include, libuhdm.a)
# This module defines:
# UHDM_INCLUDE_DIR, directory containing headers
# UHDM_LIBRARY, path to library (either static or shared)
#
# this might fail
# https://gitlab.kitware.com/cmake/cmake/issues/19120

find_path(UHDM_INCLUDE_DIRS uhdm/uhdm.h
  PATHS ${UHDM_ROOT}/include
  HINTS /usr /usr/local /usr/local/Homebrew ~/homebrew/ /opt/homebrew/
  PATH_SUFFIXES include uhdm uhdm/include include/uhdm
  NO_CMAKE_SYSTEM_PATH
  NO_SYSTEM_ENVIRONMENT_PATH)

find_path(UHDM_LIB_DIR
  NAMES libUHDM.a libuhdm.a libUHDM.so libuhdm.so libUHDM.dylib  libuhdm.dylib
  PATHS ${UHDM_ROOT}/lib
  HINTS /usr /usr/local /usr/local/Homebrew ~/homebrew/ /opt/homebrew/
  PATH_SUFFIXES lib uhdm uhdm/lib lib/uhdm
  NO_CMAKE_SYSTEM_PATH
  NO_SYSTEM_ENVIRONMENT_PATH)

if(BUILD_SHARED_LIBS)
  find_file(UHDM_LIBRARY
    NAMES libUHDM.so libuhdm.so libUHDM.dylib libuhdm.dylib
    PATHS ${UHDM_LIB_DIR}
    HINTS /usr /usr/local /usr/local/Homebrew ~/homebrew/ /opt/homebrew/
    PATH_SUFFIXES lib uhdm uhdm/lib lib/uhdm
    NO_CMAKE_SYSTEM_PATH
    NO_SYSTEM_ENVIRONMENT_PATH)
else()
  find_file(UHDM_LIBRARY
    NAMES libUHDM.a libuhdm.a
    PATHS ${UHDM_LIB_DIR}
    HINTS /usr /usr/local /usr/local/Homebrew ~/homebrew/ /opt/homebrew/
    PATH_SUFFIXES lib uhdm uhdm/lib lib/uhdm
    NO_CMAKE_SYSTEM_PATH
    NO_SYSTEM_ENVIRONMENT_PATH)
endif()


include(FindPackageHandleStandardArgs)

find_package_handle_standard_args(UHDM REQUIRED_VARS  UHDM_INCLUDE_DIRS UHDM_LIBRARY)

