#########################################################################
# Build ccache
#########################################################################

export LD_LIBRARY_PATH=/usr/local/lib64/:/usr/lib64/:$LD_LIBRARY_PATH
export CXX=`which g++` ; export CC=`which gcc`
[ -f /usr/bin/g++-7 ] && export CXX=`which g++-7` ; export CC=`which gcc-7`
[ -f /usr/local/bin/g++-7 ] && export CXX=`which g++-7` ; export CC=`which gcc-7` 

$CXX --version
echo $?


mkdir -p ../ccache
cd ../ccache
wget https://github.com/ccache/ccache/releases/download/v3.7.5/ccache-3.7.5.tar.gz
tar xvzf ccache-3.7.5.tar.gz
cd ccache-3.7.5
./configure --prefix=$PWD/../ccache
make -j 4
make install
