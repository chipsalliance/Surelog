// Width-related constants
`define INST_WIDTH     32
`define REG_ADDR_WIDTH  5
`define XPR_LEN        32
`define DOUBLE_XPR_LEN 64
`define LOG2_XPR_LEN    5
`define SHAMT_WIDTH     5

`define RV_NOP `INST_WIDTH'b0010011

// Opcodes

`define RV32_LOAD     7'b0000011
`define RV32_STORE    7'b0100011
`define RV32_MADD     7'b1000011
`define RV32_BRANCH   7'b1100011

`define RV32_LOAD_FP  7'b0000111
`define RV32_STORE_FP 7'b0100111 
`define RV32_MSUB     7'b1000111
`define RV32_JALR     7'b1100111

`define RV32_CUSTOM_0 7'b0001011
`define RV32_CUSTOM_1 7'b0101011
`define RV32_NMSUB    7'b1001011
// 7'b1101011 is reserved

`define RV32_MISC_MEM 7'b0001111
`define RV32_AMO      7'b0101111
`define RV32_NMADD    7'b1001111
`define RV32_JAL      7'b1101111

`define RV32_OP_IMM   7'b0010011
`define RV32_OP       7'b0110011
`define RV32_OP_FP    7'b1010011
`define RV32_SYSTEM   7'b1110011

`define RV32_AUIPC    7'b0010111
`define RV32_LUI      7'b0110111
// 7'b1010111 is reserved
// 7'b1110111 is reserved

// 7'b0011011 is RV64-specific
// 7'b0111011 is RV64-specific
`define RV32_CUSTOM_2 7'b1011011
`define RV32_CUSTOM_3 7'b1111011

// Arithmetic FUNCT3 encodings

`define RV32_FUNCT3_ADD_SUB 0
`define RV32_FUNCT3_SLL     1
`define RV32_FUNCT3_SLT     2
`define RV32_FUNCT3_SLTU    3
`define RV32_FUNCT3_XOR     4
`define RV32_FUNCT3_SRA_SRL 5
`define RV32_FUNCT3_OR      6
`define RV32_FUNCT3_AND     7

// Branch FUNCT3 encodings

`define RV32_FUNCT3_BEQ  0
`define RV32_FUNCT3_BNE  1
`define RV32_FUNCT3_BLT  4
`define RV32_FUNCT3_BGE  5
`define RV32_FUNCT3_BLTU 6
`define RV32_FUNCT3_BGEU 7

// MISC-MEM FUNCT3 encodings
`define RV32_FUNCT3_FENCE   0
`define RV32_FUNCT3_FENCE_I 1

// SYSTEM FUNCT3 encodings

`define RV32_FUNCT3_PRIV   0
`define RV32_FUNCT3_CSRRW  1
`define RV32_FUNCT3_CSRRS  2
`define RV32_FUNCT3_CSRRC  3
`define RV32_FUNCT3_CSRRWI 5
`define RV32_FUNCT3_CSRRSI 6
`define RV32_FUNCT3_CSRRCI 7

// PRIV FUNCT12 encodings

`define RV32_FUNCT12_ECALL  12'b000000000000
`define RV32_FUNCT12_EBREAK 12'b000000000001
`define RV32_FUNCT12_ERET   12'b000100000000
`define RV32_FUNCT12_WFI    12'b000100000010

// RV32M encodings
`define RV32_FUNCT7_MUL_DIV 7'd1

`define RV32_FUNCT3_MUL    3'd0
`define RV32_FUNCT3_MULH   3'd1
`define RV32_FUNCT3_MULHSU 3'd2
`define RV32_FUNCT3_MULHU  3'd3
`define RV32_FUNCT3_DIV    3'd4
`define RV32_FUNCT3_DIVU   3'd5
`define RV32_FUNCT3_REM    3'd6
`define RV32_FUNCT3_REMU   3'd7
