#!/bin/bash

set -uo pipefail
set -e
set -vx

# We're fairly limited as to what we want to bother to run on CentOS6
# It's fairly old and some of the things (e.g. build+run qemu) we don't
# want to bother doing.

export CROSS=/opt/cross/gcc-4.8.0-nolibc/powerpc64-linux/bin/powerpc64-linux-

MAKE_J=`grep -c processor /proc/cpuinfo`

make -j${MAKE_J} all
# Disable 'make check' for now, some errors with gcc 4.ancient
#make -j${MAKE_J} check
#(make clean; cd external/gard && CROSS= make -j${MAKE_J})
#(cd external/pflash; make -j${MAKE_J})
make clean
SKIBOOT_GCOV=1 make -j${MAKE_J}
#SKIBOOT_GCOV=1 make -j${MAKE_J} check

make clean
rm -rf builddir
mkdir builddir
make SRC=`pwd` -f ../Makefile -C builddir -j${MAKE_J}
make clean
