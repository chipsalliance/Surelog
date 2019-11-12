#!/bin/bash
set -e
# Any subsequent(*) commands which fail will cause the shell script to exit immediately

export CXX=`which g++` ; export CC=`which gcc`
# For Travis build
if test -f /usr/bin/g++-7 || test -f /usr/local/bin/g++-7 ; then
   export CXX=`which g++-7` ; 
   export CC=`which gcc-7` ;  
fi

$CXX --version
echo $?

# Complete Surelog build script (Only debug target)

echo "Generating Antlr parser"
cd ../G4
ant compile_cpp
ant copy_cpp
cd ../SVIncCompil


echo "Removing previous build"
rm -rf build/Debug
echo "Removing previous dist"
[ -d "dist/Debug" ] && chmod 777 -R dist/Debug
rm -rf dist/Debug

echo "Generating caching scheme"
cd Cache; ./build_fbs.sh;
cd ..;

echo "Generating code"
SourceCompile/generate_parser_listener.tcl
API/generate_python_listener_api.tcl 
API/embed_python_api.tcl

echo "Make"
make -j 4 GPP=${CXX};

echo "Make the release"
./release.tcl "debug" mt=0;

echo "End build"
