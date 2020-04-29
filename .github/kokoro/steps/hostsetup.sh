#!/bin/bash

set -e

echo
echo "========================================"
echo "Host adding PPAs"
echo "----------------------------------------"
sudo apt-add-repository 'ppa:ubuntu-toolchain-r/test'
wget -O - https://apt.kitware.com/keys/kitware-archive-latest.asc 2>/dev/null | sudo apt-key add -
sudo add-apt-repository 'deb https://apt.kitware.com/ubuntu/ xenial main'
echo "----------------------------------------"

echo
echo "========================================"
echo "Host updating packages"
echo "----------------------------------------"
sudo apt-get update
echo "----------------------------------------"

echo
echo "========================================"
echo "Host install packages"
echo "----------------------------------------"
# We need to remove cmake (which is in an ancient version in kokoro) before
# reinstalling a new cmake and cmake-data as the new cmake-data contains
# a file that was previously installed with cmake and thus conflicts.
sudo apt-get remove -y cmake

sudo apt-get install -y \
        ant \
        bash \
        build-essential \
        cmake cmake-data \
        coreutils \
        default-jre \
        git \
        google-perftools \
        libgoogle-perftools-dev \
        make \
        pkg-config \
        python3 \
        python3-dev \
        swig \
        tclsh \
        uuid-dev \


sudo apt-get install -y \
        g++-7 \
        g++-8 \
        g++-9 \
        gcc-7 \
        gcc-8 \
        gcc-9 \

echo
echo "========================================"
echo "Setting up compiler infrastructure"
echo "----------------------------------------"
# g++
sudo update-alternatives --install /usr/bin/g++ g++ /usr/bin/g++-9 150
sudo update-alternatives --install /usr/bin/g++ g++ /usr/bin/g++-8 100
sudo update-alternatives --install /usr/bin/g++ g++ /usr/bin/g++-7 50
# gcc
sudo update-alternatives --install /usr/bin/gcc gcc /usr/bin/gcc-9 150
sudo update-alternatives --install /usr/bin/gcc gcc /usr/bin/gcc-8 100
sudo update-alternatives --install /usr/bin/gcc gcc /usr/bin/gcc-7 50
# set alternatives
sudo update-alternatives --set g++ /usr/bin/g++-7
sudo update-alternatives --set gcc /usr/bin/gcc-7
sudo update-alternatives --set cc /usr/bin/gcc
sudo update-alternatives --set c++ /usr/bin/g++

if [ -z "${BUILD_TOOL}" ]; then
    export BUILD_TOOL=make
fi

echo "----------------------------------------"
