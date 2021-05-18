#!/bin/bash

set -uo pipefail
set -e
set -vx

MAKE_J=$(grep -c processor /proc/cpuinfo)
export CROSS="ccache powerpc64-linux-gnu-"

# There's a bug in dtc v1.4.7 packaged on fedora 28 that makes our device tree
# tests fail, so for the moment, build a slightly older DTC
git clone --depth=1 -b v1.4.4 https://git.kernel.org/pub/scm/utils/dtc/dtc.git
(cd dtc; make -j${MAKE_J})
export PATH=`pwd`/dtc:$PATH

make -j${MAKE_J} all
make -j${MAKE_J} check
(make clean; cd external/gard && CROSS= make -j${MAKE_J})
(cd external/pflash; make -j${MAKE_J})
# GCOV build disabled for GCC 8.2
# https://github.com/open-power/skiboot/issues/206
#make clean
#SKIBOOT_GCOV=1 make -j${MAKE_J}
#SKIBOOT_GCOV=1 make -j${MAKE_J} check

make clean
rm -rf builddir
mkdir builddir
make SRC=$(pwd) -f ../Makefile -C builddir -j${MAKE_J}
make clean
