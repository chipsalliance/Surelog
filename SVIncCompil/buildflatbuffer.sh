#!/bin/bash
set -e
# Any subsequent(*) commands which fail will cause the shell script to exit immediately

#########################################################################
# Build flatbuffers
#########################################################################
echo "Building Flatbuffers"
mkdir -p ../flatbuffers
cd ../flatbuffers
cp -Rf ../third_party/flatbuffers/* .

export LD_LIBRARY_PATH=/usr/local/lib64/:/usr/lib64/:$LD_LIBRARY_PATH
export CXX=`which g++` ; export CC=`which gcc`
[ -f /usr/bin/g++-7 ] && export CXX=`which g++-7` ; export CC=`which gcc-7`
[ -f /usr/local/bin/g++-7 ] && export CXX=`which g++-7` ; export CC=`which gcc-7` 

$CXX --version
echo $?
echo "Configuring Flatbuffers"
cmake -G "Unix Makefiles"  -DCMAKE_CXX_COMPILER=$CXX -DCMAKE_CXX_FLAGS="-w -Wimplicit-fallthrough=0"  #&>  flatbuffers_configure.log
echo "Making Flatbuffers"
make -j 4 #&>  flatbuffers_compile.log
echo "Testing Flatbuffers"
./flattests  &>  flatbuffers_test.log

echo "Done Building Flatbuffers"

