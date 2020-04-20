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

if [ -z "${BUILD_TOOL}" ]; then
    export BUILD_TOOL=make
fi

echo "----------------------------------------"
