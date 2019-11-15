#!/bin/bash
set -e
# Any subsequent(*) commands which fail will cause the shell script to exit immediately

# Complete Surelog build script (Only builds the release executable)
echo "Building Surelog"
./buildflatbuffer.sh
./buildantlr_mini.sh

export CXX=`which g++` ; export CC=`which gcc`
# For Travis build
if test -f /usr/bin/g++-7 || test -f /usr/local/bin/g++-7 ; then
   export CXX=`which g++-7` ; 
   export CC=`which gcc-7` ;  
fi

$CXX --version
echo $?

echo "Generating Antlr parser"
cd ../grammar
ant compile_cpp
cd ../src

echo "Generating caching scheme"
cd Cache;
../../flatbuffers/flatc header.fbs --cpp --binary 
../../flatbuffers/flatc preproc.fbs --cpp --binary 
../../flatbuffers/flatc parser.fbs --cpp --binary 
../../flatbuffers/flatc python_api.fbs --cpp --binary
cd ..;

echo "Generating code"
SourceCompile/generate_parser_listener.tcl
API/generate_python_listener_api.tcl 
API/embed_python_api.tcl
swig -c++ -python  -o API/slapi_wrap.cxx API/slapi.i
API/embed_python_api.tcl
API/generate_python_listener_api.tcl
#SourceCompile/generate_parser_listener.tcl

echo "Make"
mkdir -p build
cd build
cmake ../ -DCMAKE_CXX_COMPILER=$CXX -DCMAKE_BUILD_TYPE=Release # -DCMAKE_VERBOSE_MAKEFILE=on
make -j 4
echo "Done Building Surelog"

cd ..
echo "Run Tests"
./release.tcl  "release tcmalloc" ;
cd Testcases/ ;
./regression.tcl show_diff mt=0


echo "End Surelog Tests"


