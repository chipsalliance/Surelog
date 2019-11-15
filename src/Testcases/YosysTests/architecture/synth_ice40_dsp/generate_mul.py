#!/usr/bin/env python3

from common_mul import gen_mul

ARange = ['16','16s','17','17s','24','24s','31','31s','32','32s','33','33s','47','47s','48','48s','49','49s']
BRange = ['15','15s','16','16s','17','17s','24','24s','31','31s','32','32s']

if __name__ == "__main__":
    gen_mul(ARange, BRange, "ABP")
