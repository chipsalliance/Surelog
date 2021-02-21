#include "riscv_test.h"

#if __riscv_xlen == 64
# define STORE    sd
# define LOAD     ld
# define REGBYTES 8
#else
# define STORE    sw
# define LOAD     lw
# define REGBYTES 4
#endif

#define STACK_TOP (_end + 4096)

#define MTIME_ADDR    0x0030bff8
#define MTIMECMP_ADDR 0x00304000

  .section ".text.init","ax",@progbits
  .globl _start
  .align 2
_start:
  j handle_reset

  /* NMI vector */
  .align 2
nmi_vector:
  j wtf

  .align 2
trap_vector:
  csrrw sp, mscratch, sp
  sd t0, 5*REGBYTES(sp)
  sd t1, 6*REGBYTES(sp)

  csrr t0, mcause
  li t1, CAUSE_USER_ECALL
  beq t0, t1, ecall_handler
  bltz t0, timer_handler
  li a0, -1

ecall_handler:
  li t0, CAUSE_USER_ECALL
  csrr t1, mcause
  beq t0, t1, 1f
  li a0, 0xffff
1:
  csrr t0, mhartid
  li t1, 0x00102000
  slli t0, t0, 3
  add t0, t0, t1
  sd a0, 0(t0)
2:
  j 2b

timer_handler: 
  li t0, MTIME_ADDR
  ld t1, 0(t0)
  addi t1, t1, 500
  li t0, MTIMECMP_ADDR
  sd t1, 0(t0)
1:
  csrr t0, mip
  andi t0, t0, MIP_MTIP
  bnez t0, 1b
  
  ld t0, 5*REGBYTES(sp)
  ld t1, 6*REGBYTES(sp)
  csrrw sp, mscratch, sp
  mret

handle_reset:
  li t0, MIP_MTIP
  csrw mie, t0
  la t0, trap_vector
  csrw mtvec, t0
  la sp, STACK_TOP - SIZEOF_TRAPFRAME_T
  csrw mscratch, sp
  call extra_boot
  la a0, userstart
  j vm_boot

  .globl  pop_tf
pop_tf:
  LOAD  t0,33*REGBYTES(a0)
  csrw  sepc,t0
  LOAD  x1,1*REGBYTES(a0)
  LOAD  x2,2*REGBYTES(a0)
  LOAD  x3,3*REGBYTES(a0)
  LOAD  x4,4*REGBYTES(a0)
  LOAD  x5,5*REGBYTES(a0)
  LOAD  x6,6*REGBYTES(a0)
  LOAD  x7,7*REGBYTES(a0)
  LOAD  x8,8*REGBYTES(a0)
  LOAD  x9,9*REGBYTES(a0)
  LOAD  x11,11*REGBYTES(a0)
  LOAD  x12,12*REGBYTES(a0)
  LOAD  x13,13*REGBYTES(a0)
  LOAD  x14,14*REGBYTES(a0)
  LOAD  x15,15*REGBYTES(a0)
  LOAD  x16,16*REGBYTES(a0)
  LOAD  x17,17*REGBYTES(a0)
  LOAD  x18,18*REGBYTES(a0)
  LOAD  x19,19*REGBYTES(a0)
  LOAD  x20,20*REGBYTES(a0)
  LOAD  x21,21*REGBYTES(a0)
  LOAD  x22,22*REGBYTES(a0)
  LOAD  x23,23*REGBYTES(a0)
  LOAD  x24,24*REGBYTES(a0)
  LOAD  x25,25*REGBYTES(a0)
  LOAD  x26,26*REGBYTES(a0)
  LOAD  x27,27*REGBYTES(a0)
  LOAD  x28,28*REGBYTES(a0)
  LOAD  x29,29*REGBYTES(a0)
  LOAD  x30,30*REGBYTES(a0)
  LOAD  x31,31*REGBYTES(a0)
  LOAD  a0,10*REGBYTES(a0)
  sret

  .global  trap_entry
  .align 2
trap_entry:
  csrrw sp, sscratch, sp

  # save gprs
  STORE  x1,1*REGBYTES(sp)
  STORE  x3,3*REGBYTES(sp)
  STORE  x4,4*REGBYTES(sp)
  STORE  x5,5*REGBYTES(sp)
  STORE  x6,6*REGBYTES(sp)
  STORE  x7,7*REGBYTES(sp)
  STORE  x8,8*REGBYTES(sp)
  STORE  x9,9*REGBYTES(sp)
  STORE  x10,10*REGBYTES(sp)
  STORE  x11,11*REGBYTES(sp)
  STORE  x12,12*REGBYTES(sp)
  STORE  x13,13*REGBYTES(sp)
  STORE  x14,14*REGBYTES(sp)
  STORE  x15,15*REGBYTES(sp)
  STORE  x16,16*REGBYTES(sp)
  STORE  x17,17*REGBYTES(sp)
  STORE  x18,18*REGBYTES(sp)
  STORE  x19,19*REGBYTES(sp)
  STORE  x20,20*REGBYTES(sp)
  STORE  x21,21*REGBYTES(sp)
  STORE  x22,22*REGBYTES(sp)
  STORE  x23,23*REGBYTES(sp)
  STORE  x24,24*REGBYTES(sp)
  STORE  x25,25*REGBYTES(sp)
  STORE  x26,26*REGBYTES(sp)
  STORE  x27,27*REGBYTES(sp)
  STORE  x28,28*REGBYTES(sp)
  STORE  x29,29*REGBYTES(sp)
  STORE  x30,30*REGBYTES(sp)
  STORE  x31,31*REGBYTES(sp)

  csrrw  t0,sscratch,sp
  STORE  t0,2*REGBYTES(sp)

  # get sr, epc, badvaddr, cause
  csrr   t0,sstatus
  STORE  t0,32*REGBYTES(sp)
  csrr   t0,sepc
  STORE  t0,33*REGBYTES(sp)
  csrr   t0,sbadaddr
  STORE  t0,34*REGBYTES(sp)
  csrr   t0,scause
  STORE  t0,35*REGBYTES(sp)

  move  a0, sp
  j handle_trap
