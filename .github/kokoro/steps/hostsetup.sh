#!/bin/bash

set -e

echo
echo "========================================"
echo "Host adding PPAs"
echo "----------------------------------------"
sudo apt-add-repository 'ppa:ubuntu-toolchain-r/test'
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
sudo apt-get install -y \
        ant \
        bash \
        build-essential \
        cmake \
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
	gcc-7 \
	libgcc-7-dev \


sudo update-alternatives --remove-all gcc || true
sudo update-alternatives --remove-all g++ || true
sudo update-alternatives --install /usr/bin/gcc gcc /usr/bin/gcc-7 10
sudo update-alternatives --install /usr/bin/g++ g++ /usr/bin/g++-7 10

sudo update-alternatives --install /usr/bin/cc cc /usr/bin/gcc 30
sudo update-alternatives --set cc /usr/bin/gcc
sudo update-alternatives --install /usr/bin/c++ c++ /usr/bin/g++ 30
sudo update-alternatives --set c++ /usr/bin/g++


if [ -z "${BUILD_TOOL}" ]; then
    export BUILD_TOOL=make
fi

echo "----------------------------------------"
