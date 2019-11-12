#########################################################################
# Build ccache
#########################################################################

export CXX=`which g++` ; export CC=`which gcc`
# For Travis build
if test -f /usr/bin/g++-7 || test -f /usr/local/bin/g++-7 ; then
   export CXX=`which g++-7` ; 
   export CC=`which gcc-7` ;  
fi

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
