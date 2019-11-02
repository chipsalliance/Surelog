#########################################################################
# Build python
#########################################################################
mkdir -p ../python3.6
cd ../python3.6
wget https://www.python.org/ftp/python/3.6.1/Python-3.6.1.tgz
tar xvzf Python-3.6.1.tgz
cd Python-3.6.1
./configure --prefix=$PWD/../python
make -j 4
make install 
