#!/bin/bash
set -e
# Any subsequent(*) commands which fail will cause the shell script to exit immediately

#########################################################################
# Build python
#########################################################################
mkdir -p ../python3.6
cd ../python3.6
wget https://www.python.org/ftp/python/3.6.1/Python-3.6.1.tgz
tar xvzf Python-3.6.1.tgz
cd Python-3.6.1
./configure --prefix=$PWD/../python
echo "Building Python..."
make -j 4 > make.log
echo "Installing Python..."
make install > install.log
