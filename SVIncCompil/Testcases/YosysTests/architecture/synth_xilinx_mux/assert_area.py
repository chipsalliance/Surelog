#!/usr/bin/python3

import glob
import re
import os

re_mux = re.compile(r'mux_(index|case|if_bal|if_unbal)_(\d+)_(\d+)\.v')

area = {}
#             1  2  3  4  5  6 F7 F8
area[2]   = [ 0, 0, 1, 0, 0, 0, 0, 0 ]
area[3]   = [ 0, 0, 0, 0, 1, 0, 0, 0 ]
area[4]   = [ 0, 0, 0, 0, 0, 0, 2, 1 ]
area[5]   = [ 0, 0, 1, 0, 0, 0, 2, 1 ]
area[7]   = [ 0, 0, 3, 0, 0, 0, 2, 1 ]
area[8]   = [ 0, 0, 4, 0, 0, 0, 2, 1 ]
area[9]   = [ 0, 0, 3, 0, 1, 0, 2, 1 ]
area[15]  = [ 0, 0, 0, 0, 1, 3, 2, 1 ]
area[16]  = [ 0, 0, 0, 0, 0, 4, 2, 1 ]
area[17]  = [ 0, 0, 1, 0, 0, 4, 2, 1 ]
area[31]  = [ 0, 0, 1, 0, 1, 7, 4, 2 ]
area[32]  = [ 0, 0, 1, 0, 0, 8, 4, 2 ]
area[33]  = [ 0, 0, 0, 0, 1, 8, 4, 2 ]
area[63]  = [ 0, 0, 0, 0, 1,15,10, 5 ]
area[64]  = [ 0, 0, 0, 0, 0,16,10, 5 ]
area[65]  = [ 0, 0, 1, 0, 0,16,10, 5 ]
area[127] = [ 0, 0, 4, 0, 1,31,18, 9 ]
area[128] = [ 0, 0, 4, 0, 0,32,18, 9 ]
area[129] = [ 0, 0, 3, 0, 1,32,18, 9 ]
area[255] = [ 0, 0, 0, 0, 1,67,34,17 ]
area[256] = [ 0, 0, 0, 0, 0,68,34,17 ]
area[257] = [ 0, 0, 1, 0, 0,68,34,17 ]

for fn in glob.glob('*.v'):
    m = re_mux.match(fn)
    if not m: continue

    N,W = map(int, m.group(2,3))
    assert N in area

    bn,_ = os.path.splitext(fn)

    with open(fn, 'a') as f:
        assert_area = ['select t:{0} -assert-count {1}'.format(r,v*W) for r,v in zip(['LUT1','LUT2','LUT3','LUT4','LUT5','LUT6','MUXF7','MUXF8'], area[N])]
        print('''
`ifndef _AUTOTB
module __test ;
    wire [4095:0] assert_area = "cd; %s";
endmodule
`endif
''' % '; '.join(assert_area), file=f)
