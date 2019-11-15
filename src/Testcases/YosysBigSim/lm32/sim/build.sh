#!/bin/sh
set -ex

# this works on CentOS 6.5 with diamond_2_2-lm-101-i386-linux.rpm from lattice
export PATH=/usr/local/latticemicosystem/2.2/micosystem/gtools/lm32/bin:$PATH
export LD_LIBRARY_PATH=/usr/local/latticemicosystem/2.2/micosystem/gtools/lm32/lib

# .. or build it from the gcc sources with ../configure --target=lm32-elf
# (see build instructions in README at https://github.com/m-labs/misoc)

lm32-elf-gcc -Tlinker.ld -fno-builtin -mbarrel-shift-enabled -nostdlib -o sieve.elf crt.S sieve.c
lm32-elf-objcopy -O binary sieve.elf sieve.bin
hexdump -e '"@%07.7_ax  " 16/1 "%02x " "\n"' sieve.bin | grep '^@' > sieve.vh
rm -f sieve.elf sieve.bin
