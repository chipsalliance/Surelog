#!/bin/bash
set -e
# Any subsequent(*) commands which fail will cause the shell script to exit immediately


#########################################################################
# Build Antlr4.72 for Java and C++ 
#########################################################################
echo "Building Antlr"

# From the internet
#mkdir -p ../antlr4
#cd ../antlr4
#wget https://github.com/antlr/antlr4/archive/4.7.2.zip
#unzip 4.7.2.zip
#cp -R ../third_party/antlr4/runtime/*              antlr4-4.7.2/runtime
#cd antlr4-4.7.2
#export MAVEN_OPTS="-Xmx1G"   
#mvn clean                   
#mvn -DskipTests install

# From the localc copy
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
cmake .. -DCMAKE_BUILD_TYPE=Release -DCMAKE_CXX_COMPILER=/usr/bin/g++-7 -DCMAKE_CXX_FLAGS="-fno-builtin-malloc -fno-builtin-calloc -fno-builtin-realloc -fno-builtin-free"
make -j 4
DESTDIR=../../../runtime/Cpp/run make install

# Debug version:
cd ../../
cp -r Cpp Cpp-Debug
cd Cpp-Debug
rm -rf build run
mkdir build && mkdir run && cd build
cmake .. -DCMAKE_CXX_COMPILER=/usr/bin/g++-7 -DCMAKE_BUILD_TYPE=Debug
make -j 4
DESTDIR=../../../runtime/Cpp-Debug/run make install

# Memory Sanitizer version:
cd ../../
cp -r Cpp Cpp-AdvancedDebug
cd Cpp-AdvancedDebug
rm -rf build run
mkdir build && mkdir run && cd build
cmake .. -DCMAKE_CXX_COMPILER=/usr/bin/g++-7 -DCMAKE_BUILD_TYPE=Debug  -DCMAKE_CXX_FLAGS="-D_GLIBCXX_DEBUG=1 -fsanitize=address -fno-omit-frame-pointer"
make -j 4
DESTDIR=../../../runtime/Cpp-AdvancedDebug/run make install
echo "Done Building Antlr"
