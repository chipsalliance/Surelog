#!/usr/bin/python3

import glob
import re
import os

re_mux = re.compile(r'(mul|muladd|macc)_(\d+)(s?)_(\d+)(s?)(_(\d+)(s?))?_(A?B?C?M?P?)_A?B?C?M?P?\.v')

for fn in glob.glob('*.v'):
    m = re_mux.match(fn)
    if not m: continue

    macc = m.group(1) == 'macc'
    muladd = m.group(1) == 'muladd'
    A,B = map(int, m.group(2,4))
    Asigned,Bsigned = m.group(3,5)
    if m.group(6):
        C = int(m.group(7))
        Csigned = m.group(8)
    else:
        C = 0
    Areg = 'A' in m.group(9)
    Breg = 'B' in m.group(9)
    Mreg = 'M' in m.group(9)
    Preg = 'P' in m.group(9) or macc
    if A < B:
        A,B = B,A
        Asigned,Bsigned = Bsigned,Asigned
    if not (Asigned and Bsigned):
        A += 1
        B += 1
        Asigned = Bsigned = 1
    if C > 0 and not Csigned:
        C += 1
        Csigned = 1
    X = 1 + max(0,A-25+16) // 17
    Y = 1 + max(0,B-18+16) // 17
    count_MAC = X * Y

    count_DFF = 0
    if Mreg and (A > 25 or B > 18):
        count_DFF += A + B
        if not macc and (A > 25) ^ (B > 18):
            count_DFF -= 1 # For pure multipliers with just one big dimension,
                           #   expect last slice to absorb at least one register
    if Preg and (A > 25 or B > 18 or C > 48):
        count_DFF += max(A + B, C)
        if macc:
            count_DFF += 5 # In my testcases, accumulator is always
                           # 5bits bigger than multiplier result
        elif ((A > 25) ^ (B > 18)) and C <= 48:
            count_DFF -= 1 # For pure multipliers with just one big dimension,
                           #   expect last slice to absorb at least one register
    # TODO: More assert on number of CARRY and LUTs
    count_CARRY = ''
    if macc or muladd:
        if A <= 25 and B <= 18 and C <= 48:
            count_CARRY = '; select t:XORCY -assert-none; select t:LUT* -assert-none';
    elif A <= 25 or B <= 18:
        count_CARRY = '; select t:XORCY -assert-none; select t:LUT* -assert-none';

    bn,_ = os.path.splitext(fn)

    with open(fn, 'a') as f:
        print('''
`ifndef _AUTOTB
module __test ;
    wire [4095:0] assert_area = "cd {0}; select t:DSP48E1 -assert-max {1}; select t:FD* -assert-max {2}{3}";
endmodule
`endif
'''.format(os.path.splitext(fn)[0], count_MAC, count_DFF, count_CARRY), file=f)
