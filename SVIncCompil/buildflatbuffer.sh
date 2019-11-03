#########################################################################
# Build flatbuffers
#########################################################################
echo "Making Flatbuffers"

mkdir -p ../flatbuffers
cd ../flatbuffers
cp -Rf ../third_party/flatbuffers/* .
export CXX=/usr/local/bin/g++
cmake -G "Unix Makefiles" -DCMAKE_CXX_FLAGS="-Wimplicit-fallthrough=0"
make -j 4
./flattests
echo "Done Making Flatbuffers"

