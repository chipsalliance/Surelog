///////////////////////////////////////////////////////////////////////////////
// RISC-V ISA package (based on isa spec)
///////////////////////////////////////////////////////////////////////////////
// Copyright 2022 Iztok Jeras
//
// Licensed under the Apache License, Version 2.0 (the "License");
// you may not use this file except in compliance with the License.
// You may obtain a copy of the License at
//
//     http://www.apache.org/licenses/LICENSE-2.0
//
// Unless required by applicable law or agreed to in writing, software
// distributed under the License is distributed on an "AS IS" BASIS,
// WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
// See the License for the specific language governing permissions and
// limitations under the License.
///////////////////////////////////////////////////////////////////////////////

package riscv_isa_pkg;

///////////////////////////////////////////////////////////////////////////////
// instruction size (in bytes)
///////////////////////////////////////////////////////////////////////////////

function automatic int unsigned opsiz (logic [16-1:0] op);
priority casez (op)
//16'b????_????_?1111111:  opsiz = 10 + 2 * op[14:12];
//16'b????_????_?0111111:  opsiz = 8;
//16'b????_????_??011111:  opsiz = 6;
//16'b????_????_???111??,
  16'b????_????_??????11:  opsiz = 4;
  default               :  opsiz = 2;
endcase
endfunction: opsiz

///////////////////////////////////////////////////////////////////////////////
// 32-bit instruction format
///////////////////////////////////////////////////////////////////////////////

// base opcode map
typedef enum logic [6:2] {
  LOAD   = 5'b00_000,  LOAD_FP  = 5'b00_001,  CUSTON_0   = 5'b00_010,  MISC_MEM = 5'b00_011,  OP_IMM = 5'b00_100,  AUIPC      = 5'b00_101,  OP_IMM_32 = 5'b00_110,  OP_48_1 = 5'b00_111,
  STORE  = 5'b01_000,  STORE_FP = 5'b01_001,  CUSTOM_1   = 5'b01_010,  AMO      = 5'b01_011,  OP     = 5'b01_100,  LUI        = 5'b01_101,  OP_32     = 5'b01_110,  OP_64   = 5'b01_111,
  MADD   = 5'b10_000,  MSUB     = 5'b10_001,  NMSUB      = 5'b10_010,  NMADD    = 5'b10_011,  OP_FP  = 5'b10_100,  RESERVED_6 = 5'b10_101,  CUSTOM_2  = 5'b10_110,  OP_48_2 = 5'b10_111,
  BRANCH = 5'b11_000,  JALR     = 5'b11_001,  RESERVED_A = 5'b11_010,  JAL      = 5'b11_011,  SYSTEM = 5'b11_100,  RESERVED_D = 5'b11_101,  CUSTOM_3  = 5'b11_110,  OP_80   = 5'b11_111
} op32_op62_et;

typedef logic [3-1:0] fn3_t;

// base opcode map
typedef struct packed {
  op32_op62_et opc;  // base opcode
  logic [1:0]  c11;  // constant 2'b11 got
} op32_opcode_t;

// func3 arithetic/logic unit (R/I-type)
typedef enum logic [$bits(fn3_t)-1:0] {
  ADD   = 3'b000,  // func7[5] ? SUB : ADD
  SL    = 3'b001,  //
  SLT   = 3'b010,  //
  SLTU  = 3'b011,  //
  XOR   = 3'b100,  //
  SR    = 3'b101,  // func7[5] ? SRA : SRL
  OR    = 3'b110,  //
  AND   = 3'b111   //
} fn3_alu_et;

// func3 load unit (I-type)
typedef enum logic [$bits(fn3_t)-1:0] {
  LB  = 3'b000,  // RV32I RV64I RV128I
  LH  = 3'b001,  // RV32I RV64I RV128I
  LW  = 3'b010,  // RV32I RV64I RV128I
  LD  = 3'b011,  //       RV64I RV128I
  LBU = 3'b100,  // RV32I RV64I RV128I
  LHU = 3'b101,  // RV32I RV64I RV128I
  LWU = 3'b110,  //       RV64I RV128I
  LDU = 3'b111   //             RV128I
} fn3_ldu_et;
// NOTE: the RV128I instruction LQ (load quad) is under the MISC_MEM opcode

// func3 store (S-type)
typedef enum logic [$bits(fn3_t)-1:0] {
  SB  = 3'b000,  // RV32I RV64I RV128I
  SH  = 3'b001,  // RV32I RV64I RV128I
  SW  = 3'b010,  // RV32I RV64I RV128I
  SD  = 3'b011,  //       RV64I RV128I
  SQ  = 3'b100   //             RV128I
//    = 3'b101,  //
//    = 3'b110,  //
//    = 3'b111   //
} fn3_stu_et;

// func3 branch (B-type)
typedef enum logic [$bits(fn3_t)-1:0] {
  BEQ  = 3'b000,  //     equal
  BNE  = 3'b001,  // not equal
//     = 3'b010,
//     = 3'b011,
  BLT  = 3'b100,  // less    then            signed
  BGE  = 3'b101,  // greater then or equal   signed
  BLTU = 3'b110,  // less    then          unsigned
  BGEU = 3'b111   // greater then or equal unsigned
} fn3_bru_et;

// 32-bit instruction format structures
typedef struct packed {logic [4:0] rs3; logic [1:0] func2;          logic [4:0] rs2; logic [4:0] rs1; fn3_t func3; logic [4:0] rd     ;                       op32_opcode_t opcode;} op32_r4_t;  // Register 4 (floating point)
typedef struct packed {                 logic [6:0] func7;          logic [4:0] rs2; logic [4:0] rs1; fn3_t func3; logic [4:0] rd     ;                       op32_opcode_t opcode;} op32_r_t ;  // Register
typedef struct packed {logic [11:00] imm_11_0;                                       logic [4:0] rs1; fn3_t func3; logic [4:0] rd     ;                       op32_opcode_t opcode;} op32_i_t ;  // Immediate
typedef struct packed {logic [11:05] imm_11_5;                      logic [4:0] rs2; logic [4:0] rs1; fn3_t func3; logic [4:0] imm_4_0;                       op32_opcode_t opcode;} op32_s_t ;  // Store
typedef struct packed {logic [12:12] imm_12; logic [10:5] imm_10_5; logic [4:0] rs2; logic [4:0] rs1; fn3_t func3; logic [4:1] imm_4_1; logic [11:11] imm_11; op32_opcode_t opcode;} op32_b_t ;  // Branch
typedef struct packed {logic [31:12] imm_31_12;                                                                    logic [4:0] rd     ;                       op32_opcode_t opcode;} op32_u_t ;  // Upper immediate
typedef struct packed {logic [20:20] imm_20; logic [10:1] imm_10_1; logic [11:11] imm_11; logic [19:12] imm_19_12; logic [4:0] rd     ;                       op32_opcode_t opcode;} op32_j_t ;  // Jump

// union of 32-bit instruction formats
typedef union packed {
  op32_r4_t r4;  // Register 4
  op32_r_t  r ;  // Register
  op32_i_t  i ;  // Immediate
  op32_s_t  s ;  // Store
  op32_b_t  b ;  // Branch
  op32_u_t  u ;  // Upper immediate
  op32_j_t  j ;  // Jump
} op32_t;

endpackage: riscv_isa_pkg

///////////////////////////////////////////////////////////////////////////////
// R5P: load/store unit
///////////////////////////////////////////////////////////////////////////////
// Copyright 2022 Iztok Jeras
//
// Licensed under the Apache License, Version 2.0 (the "License");
// you may not use this file except in compliance with the License.
// You may obtain a copy of the License at
//
//     http://www.apache.org/licenses/LICENSE-2.0
//
// Unless required by applicable law or agreed to in writing, software
// distributed under the License is distributed on an "AS IS" BASIS,
// WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
// See the License for the specific language governing permissions and
// limitations under the License.
///////////////////////////////////////////////////////////////////////////////

module r5p_lsu
  import riscv_isa_pkg::*;
(
  // instruction input
  input  logic [32-1:0] ins,
  // partially decoded output
  output logic  [5-1:0] rd ,  // register destination
  output logic  [5-1:0] rs1,  // register source 1
  output logic  [5-1:0] rs2,  // register source 2
  output logic [12-1:0] imm   // immediate
);

op32_t dec;

assign dec = op32_t'(ins);

assign rd  = dec.r.rd ;
assign rs1 = dec.r.rs1;
assign rs2 = dec.r.rs2;
assign imm = dec.i.imm_11_0;

endmodule: r5p_lsu

   
