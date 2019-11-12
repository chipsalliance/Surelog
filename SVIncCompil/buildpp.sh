#!/bin/bash
set -e
# Any subsequent(*) commands which fail will cause the shell script to exit immediately


export LD_LIBRARY_PATH=/usr/local/lib64/:/usr/lib64/:$LD_LIBRARY_PATH
export CXX=`which g++` ; export CC=`which gcc` 
[ -f /usr/bin/g++-7 ] && export CXX=`which g++-7` ; export CC=`which gcc-7`
[ -f /usr/local/bin/g++-7 ] && export CXX=`which g++-7` ; export CC=`which gcc-7`

# Complete Surelog build script

echo "Generating Antlr parser"
cd ../G4
ant compile_cpp
ant copy_pp_cpp
cd ../SVIncCompil

echo "Generating caching scheme"
cd Cache; ./build_fbs.sh;
cd ..;

echo "Generating code"
SourceCompile/generate_parser_listener.tcl
API/generate_python_listener_api.tcl 
API/embed_python_api.tcl

echo "Make"
make -j 4 GPP=${CXX}
make CONF=Release -j 4 GPP=${CXX};
make CONF=ReleaseNoTcMalloc -j 4 GPP=${CXX};

echo "Run Tests"
./release.tcl ;
cd Testcases/ ;
./regression.tcl

echo "End build"
