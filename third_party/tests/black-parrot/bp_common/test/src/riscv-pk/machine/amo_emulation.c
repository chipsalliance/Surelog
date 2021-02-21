// Created to emulate AMO instructions based on LR/SC

#include "emulation.h"
#include "amo_emulation.h"

// These routines rely on the compiler to turn these operations into libcalls
// when not natively supported.  So work on making those go fast.

#define OPCODE(x)  ((x >> 0) & 0x7F)
#define RD(x)      ((x >> 7) & 0x1F)
#define FUNCT3(x)  ((x >> 12) & 0x7)
#define RS1(x)     ((x >> 15) & 0x1F)
#define RS2(x)     ((x >> 20) & 0x1F)
#define FUNCT5(x)  ((x >> 27) & 0x1F)
#define FUNCT11(x) ((x >> 20) & 0x7FF)

static uint64_t (*amow_jt[32])(uint64_t, uint64_t) =
{
  amo_addw, amo_swapw, 0, 0, amo_xorw, 0, 0, 0,
  amo_orw, 0, 0, 0, amo_andw, 0, 0, 0,
  amo_minw, 0, 0, 0, amo_maxw, 0, 0, 0,
  amo_minuw, 0, 0, 0, amo_maxuw, 0, 0, 0,
};

static uint64_t (*amod_jt[32])(uint64_t, uint64_t) = 
{
  amo_addd, amo_swapd, 0, 0, amo_xord, 0, 0, 0,
  amo_ord, 0, 0, 0, amo_andd, 0, 0, 0,
  amo_mind, 0, 0, 0, amo_maxd, 0, 0, 0,
  amo_minud, 0, 0, 0, amo_maxud, 0, 0, 0,
};

static uint64_t (**amo_jt[8])(uint64_t, uint64_t) = 
{
  0, 0, amow_jt, amod_jt, 0, 0, 0, 0
};

DECLARE_EMULATION_FUNC(emulate_amo)
{
  uintptr_t rs1 = GET_RS1(insn, regs), rs2 = GET_RS2(insn, regs), rd;
  uint8_t opcode = OPCODE(insn);
  uint8_t func3 = FUNCT3(insn);
  uint8_t func5 = FUNCT5(insn);
  uint64_t (*f)(uint64_t, uint64_t) = amo_jt[func3][func5];
  
  if(opcode != 0x2f)
    return truly_illegal_insn(regs, mcause, mepc, mstatus, insn);
  
  if(f == 0)
    return truly_illegal_insn(regs, mcause, mepc, mstatus, insn);
  else
    rd = amo_func(rs1, rs2, (uint64_t)f);

  SET_RD(insn, regs, rd);
}