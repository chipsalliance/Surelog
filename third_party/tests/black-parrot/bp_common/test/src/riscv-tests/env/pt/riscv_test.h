// See LICENSE for license details.

#ifndef _ENV_PHYSICAL_SINGLE_CORE_TIMER_H
#define _ENV_PHYSICAL_SINGLE_CORE_TIMER_H

#include "../p/riscv_test.h"

#define TIMER_INTERVAL 100
#define MTIME_ADDR    0x030bff8
#define MTIMECMP_ADDR 0x0304000

#undef EXTRA_INIT_TIMER
#define EXTRA_INIT_TIMER                                                \
        li a0, MSTATUS_MPP;                                             \
        csrs mstatus, a0;                                               \
        li a0, MSTATUS_MPIE;                                            \
        csrs mstatus, a0;                                               \
        li a0, MIP_MTIP;                                                \
        csrs mie, a0;                                                   \
        li t0, MTIME_ADDR;                                              \
        ld a0, 0(t0);                                                   \
        addi a0, a0, TIMER_INTERVAL;                                    \
        li t0, MTIMECMP_ADDR;                                           \
        sd a0, 0(t0);                                                   \

#if SSTATUS_XS != 0x18000
# error
#endif
#define XS_SHIFT 15

#undef INTERRUPT_HANDLER
#define INTERRUPT_HANDLER                                               \
        slli t5, t5, 1;                                                 \
        srli t5, t5, 1;                                                 \
        add t5, t5, -IRQ_M_TIMER;                                       \
        bnez t5, other_exception; /* other interrups shouldn't happen */\
        li t6, MTIME_ADDR;                                              \
        ld t5, 0(t6);                                                   \
        addi t5, t5, TIMER_INTERVAL;                                    \
        li t6, MTIMECMP_ADDR;                                           \
        sd t5, 0(t6);                                                   \
      1:                                                                \
        csrr t5, mip;                                                   \
        andi t5, t5, MIP_MTIP;                                          \
        bnez t5, 1b;                                                    \

#undef SAVE_REGS
#define SAVE_REGS                 \
        csrrw sp, mscratch, sp;   \
        sd t5, 0(sp);             \
        sd t6, -8(sp);            \

#undef RESTORE_REGS
#define RESTORE_REGS              \
        ld t5, 0(sp);             \
        ld t6, -8(sp);            \
        csrrw sp, mscratch, sp;   \
        mret;                     \

//-----------------------------------------------------------------------
// Data Section Macro
//-----------------------------------------------------------------------

#undef EXTRA_DATA
#define EXTRA_DATA                                                      \
        .align 3;                                                       \
regspill:                                                               \
        .dword 0xdeadbeefcafebabe;                                      \
        .dword 0xdeadbeefcafebabe;                                      \
        .dword 0xdeadbeefcafebabe;                                      \
        .dword 0xdeadbeefcafebabe;                                      \
        .dword 0xdeadbeefcafebabe;                                      \
        .dword 0xdeadbeefcafebabe;                                      \
        .dword 0xdeadbeefcafebabe;                                      \
        .dword 0xdeadbeefcafebabe;                                      \
        .dword 0xdeadbeefcafebabe;                                      \
        .dword 0xdeadbeefcafebabe;                                      \
        .dword 0xdeadbeefcafebabe;                                      \
        .dword 0xdeadbeefcafebabe;                                      \
        .dword 0xdeadbeefcafebabe;                                      \
        .dword 0xdeadbeefcafebabe;                                      \
        .dword 0xdeadbeefcafebabe;                                      \
        .dword 0xdeadbeefcafebabe;                                      \
        .dword 0xdeadbeefcafebabe;                                      \
        .dword 0xdeadbeefcafebabe;                                      \
        .dword 0xdeadbeefcafebabe;                                      \
        .dword 0xdeadbeefcafebabe;                                      \
        .dword 0xdeadbeefcafebabe;                                      \
        .dword 0xdeadbeefcafebabe;                                      \
        .dword 0xdeadbeefcafebabe;                                      \
        .dword 0xdeadbeefcafebabe;                                      \
evac:                                                                   \
        .skip 32768;                                                    \

#endif
