#!/bin/sh
set -ex
msp430-gcc -Wall -Os -o sieve.elf sieve.c
msp430-objcopy -O ihex sieve.elf sieve.ihex
python ihex2vlog.py < sieve.ihex > sieve.v
msp430-objdump -d sieve.elf
rm -f sieve.elf sieve.ihex
