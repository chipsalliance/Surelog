#!/bin/bash
set -e
# Any subsequent(*) commands which fail will cause the shell script to exit immediately

#########################################################################
# Build flatbuffers
#########################################################################
echo "Making Flatbuffers"

export CC=`which gcc-7`
export CXX=`which g++-7`
mkdir -p ../flatbuffers
cd ../flatbuffers
cp -Rf ../third_party/flatbuffers/* .
cmake -G "Unix Makefiles" -DCMAKE_CXX_COMPILER=/usr/bin/g++-7 -DCMAKE_CXX_FLAGS="-Wimplicit-fallthrough=0"  &>  flatbuffers_configure.log
make -j 4 &>  flatbuffers_compile.log
./flattests  &>  flatbuffers_test.log

echo "Done Making Flatbuffers"

