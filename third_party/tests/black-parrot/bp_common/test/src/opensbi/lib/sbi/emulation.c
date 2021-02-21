#include <stdint.h>

#include <sbi/emulation.h>
#include <sbi/sbi_trap.h>

#define CSR_ADDR_MVENDORID  0xF11
#define CSR_ADDR_MARCHID    0xF12
#define CSR_ADDR_MIMPID     0xF13
#define CSR_ADDR_MHARTID    0xF14

#define RISCV_OPCODE_SYSTEM 0b1110011
#define RISCV_OPCODE_ATOMIC 0b0101111
#define RISCV_OPCODE_OP     0b0110011

#define OPCODE(x)  ((x >> 0) & 0x7F)
#define RD(x)      ((x >> 7) & 0x1F)
#define FUNCT3(x)  ((x >> 12) & 0x7)
#define RS1(x)     ((x >> 15) & 0x1F)
#define RS2(x)     ((x >> 20) & 0x1F)
#define RS3(x)     ((x >> 27) & 0x1F)
#define FUNCT7(x)  ((x >> 25) & 0x7F)

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

static uint64_t (*mul_jt[8])(uint64_t, uint64_t) =
{
  0, mul_mulh, mul_mulhsu, mul_mulhu, 0, 0, 0, 0
};

int decode_illegal(uint64_t insn, struct sbi_trap_regs *regs) 
{
  uint8_t rs3 = RS3(insn);
  uint8_t rs2 = RS2(insn);
  uint8_t rs1 = RS1(insn);
  uint8_t funct3 = FUNCT3(insn);
  //uint8_t funct7 = FUNCT7(insn);
  uint8_t rd = RD(insn);
  uint8_t opcode = OPCODE(insn);
  
  uint64_t rs1_data = ((uint64_t*)regs)[rs1];
  uint64_t rs2_data = ((uint64_t*)regs)[rs2];

  if (opcode == RISCV_OPCODE_ATOMIC) {
    uint64_t (*f)(uint64_t, uint64_t) = amo_jt[funct3][rs3];
    ((uint64_t*)regs)[rd] = amo_func(rs1_data, rs2_data, (uint64_t)f);
    regs->mepc += 4;
    return 0;
  } else if (opcode == RISCV_OPCODE_OP) {
    ((uint64_t*)regs)[rd] = mul_jt[funct3](rs1_data, rs2_data);
    regs->mepc +=4;
    return 0;
  } else {
    // Fail on truly illegal instruction
    return -1;
  }
}

