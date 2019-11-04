#!/bin/bash
set -e
# Any subsequent(*) commands which fail will cause the shell script to exit immediately

# Complete Surelog build script (Builds all targets: debug, release...)

export CXX=`which g++-7`
export CC=`which gcc-7`

echo "Generating Antlr parser"
cd ../G4
ant compile_cpp
ant copy_cpp
cd ../SVIncCompil

echo "Removing previous build"
rm -rf build
echo "Removing previous dist"
[ -d "dist" ] && chmod 777 -R dist
rm -rf dist

echo "Generating caching scheme"
cd Cache; ./build_fbs.sh;
cd ..;

echo "Generating code"
SourceCompile/generate_parser_listener.tcl
API/generate_python_listener_api.tcl 
API/embed_python_api.tcl

echo "Make"
make -j 4
make CONF=Release -j 4;
make CONF=ReleaseNoTcMalloc -j 4;

echo "Run Tests"
./release.tcl ;
cd Testcases/ ;
./regression.tcl

echo "End build"
