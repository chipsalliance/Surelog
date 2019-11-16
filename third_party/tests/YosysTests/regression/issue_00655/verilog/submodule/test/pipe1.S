.globl _start

.text
_start:
xor r0, r0, r0

mvi r1, 10
addi r2, r1, 1
addi r3, r2, 1
muli r4, r1, 10
add r5, r4, r4

mvhi r1, 0xdead
ori r2, r0, 0xbeef
sw (r1+0), r2
