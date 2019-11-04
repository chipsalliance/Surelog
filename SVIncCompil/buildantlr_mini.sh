#!/bin/bash
set -e
# Any subsequent(*) commands which fail will cause the shell script to exit immediately

#########################################################################
# Build Antlr4.72 for Java and C++ 
#########################################################################
echo "Building Antlr"

mkdir -p ../antlr4/antlr4-4.7.2/tool/target/
mkdir -p ../antlr4/antlr4-4.7.2/runtime
mkdir -p ../antlr4/antlr4-4.7.2/tool/target/
cd ../antlr4
cp ../third_party/antlr4/antlr4-4.7.2-complete.jar antlr4-4.7.2/tool/target/
cp -R ../third_party/antlr4/runtime/*              antlr4-4.7.2/runtime
cd antlr4-4.7.2

export CC=`which gcc-7`
export CXX=`which g++-7`

# Optimized version
cd runtime/Cpp
rm -rf build run
mkdir build && mkdir run && cd build
cmake .. -DCMAKE_CXX_COMPILER=/usr/bin/g++-7 -DCMAKE_BUILD_TYPE=Release -DCMAKE_CXX_FLAGS="-fno-builtin-malloc -fno-builtin-calloc -fno-builtin-realloc -fno-builtin-free"  &>  antlr_configure.log
make -j 4 &>  antlr_compile.log
DESTDIR=../../../runtime/Cpp/run make install  &>  antlr_install.log
echo "Done Building Antlr"
