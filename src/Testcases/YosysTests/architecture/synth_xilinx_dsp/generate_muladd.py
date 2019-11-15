#!/usr/bin/env python3

from common_muladd import gen_muladd

ARange = ['24','24s','25','25s','36','36s']
BRange = ['17','17s','18','18s','19','19s']
CRange = ['32','32s','48','48s','96','96s']

if __name__ == "__main__":
    gen_muladd(['24','49s'], ['17','36s'], ['47','96s'], reg="ABMP")
    gen_muladd(ARange, BRange, CRange, reg="")
