#########################################################################
# Build ccache
#########################################################################

export CXX=`which g++-7`
export CC=`which gcc-7`

mkdir -p ../ccache
cd ../ccache
wget https://github.com/ccache/ccache/releases/download/v3.7.5/ccache-3.7.5.tar.gz
tar xvzf ccache-3.7.5.tar.gz
cd ccache-3.7.5
./configure --prefix=$PWD/../ccache
make -j 4
make install
