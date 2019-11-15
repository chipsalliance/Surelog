#!/bin/sh
set -ex
arm-linux-gnueabi-gcc -Wall -Os -marm -march=armv2a -mno-thumb-interwork -ffreestanding -nostdlib \
	-Wl,-Bstatic,-T,sections.lds,-Map,sieve.map,--strip-debug,--build-id=none,--fix-v4bx -o sieve.elf start.S sieve.c
arm-linux-gnueabi-objcopy -O ihex -j .memory sieve.elf sieve.ihex
python ihex2vlog.py < sieve.ihex > sieve.v
arm-linux-gnueabi-objdump -d sieve.elf
rm -f sieve.map sieve.elf sieve.ihex
