#!/bin/bash
set -e
# Any subsequent(*) commands which fail will cause the shell script to exit immediately

#########################################################################
# Build python
#########################################################################
echo "Making Python"
g++ --version
echo $?
mkdir -p ../python3.6
cd ../python3.6
echo "Downloading Python..."
wget https://www.python.org/ftp/python/3.6.1/Python-3.6.1.tgz &>  python_download.log
echo "Untaring Python..."
tar xvzf Python-3.6.1.tgz &>  python_tar.log
cd Python-3.6.1
echo "Configuring Python..."
./configure --prefix=$PWD/../python &>  python_configure.log
echo "Building Python..."
make -j 4 &>  python_make.log
echo "Installing Python..."
make install &>   python_install.log
echo "Done Installing Python"
