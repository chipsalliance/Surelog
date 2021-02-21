// See LICENSE for license details.

#ifndef _ENV_PHYSICAL_SINGLE_CORE_H
#define _ENV_PHYSICAL_SINGLE_CORE_H

#include "../encoding.h"

//-----------------------------------------------------------------------
// Begin Macro
//-----------------------------------------------------------------------

#define RVTEST_RV64U                                                    \
  .macro init;                                                          \
  .endm

#define RVTEST_RV64UF                                                   \
  .macro init;                                                          \
  RVTEST_FP_ENABLE;                                                     \
  .endm

#define RVTEST_RV32U                                                    \
  .macro init;                                                          \
  .endm

#define RVTEST_RV32UF                                                   \
  .macro init;                                                          \
  RVTEST_FP_ENABLE;                                                     \
  .endm

#define RVTEST_RV64M                                                    \
  .macro init;                                                          \
  RVTEST_ENABLE_MACHINE;                                                \
  .endm

#define RVTEST_RV64S                                                    \
  .macro init;                                                          \
  RVTEST_ENABLE_SUPERVISOR;                                             \
  .endm

#define RVTEST_RV32M                                                    \
  .macro init;                                                          \
  RVTEST_ENABLE_MACHINE;                                                \
  .endm

#define RVTEST_RV32S                                                    \
  .macro init;                                                          \
  RVTEST_ENABLE_SUPERVISOR;                                             \
  .endm

#if __riscv_xlen == 64
# define CHECK_XLEN li a0, 1; slli a0, a0, 31; bgez a0, 1f; RVTEST_PASS; 1:
#else
# define CHECK_XLEN li a0, 1; slli a0, a0, 31; bltz a0, 1f; RVTEST_PASS; 1:
#endif

#define INIT_PMP                                                        \
  la t0, 1f;                                                            \
  csrw mtvec, t0;                                                       \
  /* Set up a PMP to permit all accesses */                             \
  li t0, (1 << (31 + (__riscv_xlen / 64) * (53 - 31))) - 1;             \
  csrw pmpaddr0, t0;                                                    \
  li t0, PMP_NAPOT | PMP_R | PMP_W | PMP_X;                             \
  csrw pmpcfg0, t0;                                                     \
  .align 2;                                                             \
1:

#define INIT_SATP                                                      \
  la t0, 1f;                                                            \
  csrw mtvec, t0;                                                       \
  csrwi sptbr, 0;                                                       \
  .align 2;                                                             \
1:

#define DELEGATE_NO_TRAPS                                               \
  la t0, 1f;                                                            \
  csrw mtvec, t0;                                                       \
  csrwi medeleg, 0;                                                     \
  csrwi mideleg, 0;                                                     \
  csrwi mie, 0;                                                         \
  .align 2;                                                             \
1:

#define RVTEST_ENABLE_SUPERVISOR                                        \
  li a0, MSTATUS_MPP & (MSTATUS_MPP >> 1);                              \
  csrs mstatus, a0;                                                     \
  li a0, SIP_SSIP | SIP_STIP;                                           \
  csrs mideleg, a0;                                                     \

#define RVTEST_ENABLE_MACHINE                                           \
  li a0, MSTATUS_MPP;                                                   \
  csrs mstatus, a0;                                                     \

#define RVTEST_FP_ENABLE                                                \
  li a0, MSTATUS_FS & (MSTATUS_FS >> 1);                                \
  csrs mstatus, a0;                                                     \
  csrwi fcsr, 0

#define RISCV_MULTICORE_DISABLE                                         \
  csrr a0, mhartid;                                                     \
  1: bnez a0, 1b

#define EXTRA_TVEC_USER
#define EXTRA_TVEC_MACHINE
#define EXTRA_INIT
#define EXTRA_INIT_TIMER
#define SAVE_REGS
#define RESTORE_REGS

#define INTERRUPT_HANDLER j other_exception /* No interrupts should occur */

#define RVTEST_CODE_BEGIN                                               \
        .section .text.init;                                            \
        .align  6;                                                      \
        .weak stvec_handler;                                            \
        .weak mtvec_handler;                                            \
        .weak bp_mtvec_handler;                                         \
        .globl _start;                                                  \
_start:                                                                 \
        /* 0 all registers */                                           \
        addi x1,  x0, 0;                                                \
        addi x2,  x0, 0;                                                \
        addi x3,  x0, 0;                                                \
        addi x4,  x0, 0;                                                \
        addi x5,  x0, 0;                                                \
        addi x6,  x0, 0;                                                \
        addi x7,  x0, 0;                                                \
        addi x8,  x0, 0;                                                \
        addi x9,  x0, 0;                                                \
        addi x10, x0, 0;                                                \
        addi x11, x0, 0;                                                \
        addi x12, x0, 0;                                                \
        addi x13, x0, 0;                                                \
        addi x14, x0, 0;                                                \
        addi x15, x0, 0;                                                \
        addi x16, x0, 0;                                                \
        addi x17, x0, 0;                                                \
        addi x18, x0, 0;                                                \
        addi x19, x0, 0;                                                \
        addi x20, x0, 0;                                                \
        addi x21, x0, 0;                                                \
        addi x22, x0, 0;                                                \
        addi x23, x0, 0;                                                \
        addi x24, x0, 0;                                                \
        addi x25, x0, 0;                                                \
        addi x26, x0, 0;                                                \
        addi x27, x0, 0;                                                \
        addi x28, x0, 0;                                                \
        addi x29, x0, 0;                                                \
        addi x30, x0, 0;                                                \
        addi x31, x0, 0;                                                \
                                                                        \
        /* This is the BlackParrot emulation stack setup */             \
        li   sp, 0x8000CFF0;                                            \
                                                                        \
        csrr x1, mhartid;                                               \
        slli x1, x1, 13;                                                \
        sub  sp, sp, x1;                                                \
                                                                        \
        /* save the stack pointer to mscratch */                        \
        /* , so it can be used on first trap entry*/                    \
        csrw mscratch, sp;                                              \
        j reset_vector;                                                 \
        .align 2;                                                       \
trap_vector:                                                            \
        SAVE_REGS;                                                      \
        /* test whether the test came from pass/fail */                 \
        csrr t5, mcause;                                                \
        li t6, CAUSE_USER_ECALL;                                        \
        beq t5, t6, write_tohost;                                       \
        li t6, CAUSE_SUPERVISOR_ECALL;                                  \
        beq t5, t6, write_tohost;                                       \
        li t6, CAUSE_MACHINE_ECALL;                                     \
        beq t5, t6, write_tohost;                                       \
        /* if an mtvec_handler is defined, jump to it */                \
        la t5, mtvec_handler;                                           \
        beqz t5, 1f;                                                    \
        jr t5;                                                          \
        /* was it an interrupt or an exception? */                      \
  1:    csrr t5, mcause;                                                \
        bgez t5, handle_exception;                                      \
        INTERRUPT_HANDLER;                                              \
        RESTORE_REGS;                                                   \
handle_exception:                                                       \
        /* we don't know how to handle whatever the exception was */    \
        /* ... but blackparrot does! */                                 \
        la t5, bp_mtvec_handler;                                        \
        beqz t5, other_exception;                                       \
        jr t5;                                                          \
  other_exception:                                                      \
        /* some unhandlable exception occurred */                       \
  1:    ori TESTNUM, TESTNUM, 1337;                                     \
  write_tohost:                                                         \
        sw TESTNUM, tohost, t5;                                         \
        j write_tohost;                                                 \
reset_vector:                                                           \
        RISCV_MULTICORE_DISABLE;                                        \
        INIT_SATP;                                                      \
        INIT_PMP;                                                       \
        DELEGATE_NO_TRAPS;                                              \
        li TESTNUM, 0;                                                  \
        la t0, trap_vector;                                             \
        csrw mtvec, t0;                                                 \
        CHECK_XLEN;                                                     \
        /* if an stvec_handler is defined, delegate exceptions to it */ \
        la t0, stvec_handler;                                           \
        beqz t0, 1f;                                                    \
        csrw stvec, t0;                                                 \
        li t0, (1 << CAUSE_LOAD_PAGE_FAULT) |                           \
               (1 << CAUSE_STORE_PAGE_FAULT) |                          \
               (1 << CAUSE_FETCH_PAGE_FAULT) |                          \
               (1 << CAUSE_MISALIGNED_FETCH) |                          \
               (1 << CAUSE_USER_ECALL) |                                \
               (1 << CAUSE_BREAKPOINT);                                 \
        csrw medeleg, t0;                                               \
        csrr t1, medeleg;                                               \
        bne t0, t1, other_exception;                                    \
1:      csrwi mstatus, 0;                                               \
        RVTEST_ENABLE_MACHINE;                                          \
        init;                                                           \
        EXTRA_INIT;                                                     \
        EXTRA_INIT_TIMER;                                               \
        la t0, 1f;                                                      \
        csrw mepc, t0;                                                  \
        csrr a0, mhartid;                                               \
        mret;                                                           \
1:

//-----------------------------------------------------------------------
// End Macro
//-----------------------------------------------------------------------

#define RVTEST_CODE_END                                                 \
        unimp

//-----------------------------------------------------------------------
// Pass/Fail Macro
//-----------------------------------------------------------------------
// BP: Modified to work with BlackParrot termination condition
//   TODO: Finish should be a global constant
#define TESTNUM gp
#define RVTEST_PASS                                                     \
        li a0, 0;                                                       \
        li a1, 0x00102000;                                              \
        csrr a2, mhartid;                                               \
        slli a2, a2, 3;                                                 \
        add a1, a2, a1;                                                 \
        sb a0, 0(a1);                                                   \
        fence;                                                          \

// BP: Modified to work with BlackParrot termination condition
#define RVTEST_FAIL                                                     \
        li a0, -1;                                                      \
        li a1, 0x00102000;                                              \
        csrr a2, mhartid;                                               \
        slli a2, a2, 3;                                                 \
        add a1, a2, a1;                                                 \
        sb a0, 0(a1);                                                   \
        fence;                                                          \

//-----------------------------------------------------------------------
// Data Section Macro
//-----------------------------------------------------------------------

#define EXTRA_DATA

#define RVTEST_DATA_BEGIN                                               \
        EXTRA_DATA                                                      \
        .pushsection .tohost,"aw",@progbits;                            \
        .align 6; .global tohost; tohost: .dword 0;                     \
        .align 6; .global fromhost; fromhost: .dword 0;                 \
        .popsection;                                                    \
        .align 4; .global begin_signature; begin_signature:

#define RVTEST_DATA_END .align 4; .global end_signature; end_signature:

#endif
