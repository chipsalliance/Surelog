#!/bin/sh
set -ex
avr-gcc -Wall -Os -fno-inline -mmcu=avr2 -o sieve.elf sieve.c
avr-objcopy -O ihex sieve.elf sieve.ihex
python ihex2vlog.py < sieve.ihex > sieve.v
avr-objdump -d sieve.elf
rm -f sieve.elf sieve.ihex
