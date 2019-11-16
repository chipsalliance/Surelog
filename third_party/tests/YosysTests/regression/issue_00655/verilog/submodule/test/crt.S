.globl _start

.text
_start:
xor r0, r0, r0

mvhi sp, hi(_fstack)
ori sp, sp, lo(_fstack)

mv fp,r0

mvhi r1, hi(_fbss)
ori r1, r1, lo(_fbss)
mvhi r2, hi(_ebss)
ori r2, r2, lo(_ebss)

1:
bge r1, r2, 2f
sw (r1+0), r0
addi r1, r1, 4
bi 1b
2:

calli main

mvhi r1, 0xdead
ori r2, r0, 0xbeef
sw (r1+0), r2
