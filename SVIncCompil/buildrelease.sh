#!/bin/bash
set -e
# Any subsequent(*) commands which fail will cause the shell script to exit immediately

# Complete Surelog build script (Only builds the release executable)
echo "Building Surelog"

export CXX=`which g++` ; export CC=`which gcc`
# For Travis build
if test -f /usr/bin/g++-7 || test -f /usr/local/bin/g++-7 ; then
   export CXX=`which g++-7` ; 
   export CC=`which gcc-7` ;  
fi

$CXX --version
echo $?

echo "Generating Antlr parser"
cd ../G4
ant compile_cpp
ant copy_cpp
cd ../SVIncCompil

echo "Removing previous build"
rm -rf build/Release;
echo "Removing previous dist"
[ -d "dist/Release" ] && chmod 777 -R dist/Release
rm -rf dist/Release;

echo "Generating caching scheme"
cd Cache; ./build_fbs.sh;
cd ..;

echo "Generating code"
SourceCompile/generate_parser_listener.tcl
API/generate_python_listener_api.tcl 
API/embed_python_api.tcl

echo "Make"
make CONF=Release -j 4 GPP=${CXX};
echo "Done Building Surelog"

echo "Run Tests"
./release.tcl  "release tcmalloc" ;
cd Testcases/ ;
./regression.tcl show_diff mt=0


echo "End Surelog Tests"


