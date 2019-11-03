#########################################################################
# Build Antlr4.72 for Java and C++ 
#########################################################################

mkdir -p ../antlr4/antlr4-4.7.2/tool/target/
mkdir -p ../antlr4/antlr4-4.7.2/runtime
mkdir -p ../antlr4/antlr4-4.7.2/tool/target/
cd ../antlr4
cp ../third_party/antlr4/antlr4-4.7.2-complete.jar antlr4-4.7.2/tool/target/
cp -R ../third_party/antlr4/runtime/*              antlr4-4.7.2/runtime
cd antlr4-4.7.2
export CXX=`which g++`
# Optimized version
cd runtime/Cpp
rm -rf build run
mkdir build && mkdir run && cd build
cmake .. -DCMAKE_CXX_COMPILER=/usr/bin/c++ -DCMAKE_BUILD_TYPE=Release -DCMAKE_CXX_FLAGS="-fno-builtin-malloc -fno-builtin-calloc -fno-builtin-realloc -fno-builtin-free"
make -j 4
DESTDIR=../../../runtime/Cpp/run make install
