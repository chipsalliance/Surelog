#!/bin/bash
set -e
# Any subsequent(*) commands which fail will cause the shell script to exit immediately

#########################################################################
# Build flatbuffers
#########################################################################
echo "Building Flatbuffers"
g++ --version
echo $?
mkdir -p ../flatbuffers
cd ../flatbuffers
cp -Rf ../third_party/flatbuffers/* .
export LD_LIBRARY_PATH=/usr/local/lib64/:/usr/lib64/:$LD_LIBRARY_PATH
export PATH=/usr/local/bin/:$PATH
cmake -G "Unix Makefiles"  -DCMAKE_CXX_FLAGS="-w -Wimplicit-fallthrough=0" # &>  flatbuffers_configure.log
make -j 4 #&>  flatbuffers_compile.log
./flattests  #&>  flatbuffers_test.log

echo "Done Building Flatbuffers"

