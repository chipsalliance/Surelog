#!/usr/bin/env python3

from common_mul import gen_mul

ARange = ['17','17s','18','18s','19','19s','24','24s','25','25s','36','36s','49','49s','50','50s','75','75s']
BRange = ['17','17s','18','18s','19','19s','27','27s','34','34s','35','35s','36','36s']

if __name__ == "__main__":
    gen_mul(['24','49s'], ['17','36s'], reg="ABMP")
    gen_mul(ARange, BRange, reg="")
