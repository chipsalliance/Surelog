///////////////////////////////////////////////////////////////////////////////
// R5P: core
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

import riscv_isa_pkg::*;
//import riscv_csr_pkg::*;

import r5p_pkg::*;

module r5p_core #(
  // RISC-V ISA
  int unsigned XLEN = 32,   // is used to quickly switch between 32 and 64 for testing
`ifndef SYNOPSYS_VERILOG_COMPILER
  // extensions  (see `riscv_isa_pkg` for enumeration definition)
  isa_ext_t    XTEN = RV_M | RV_C | RV_Zicsr,
  // privilige modes
  isa_priv_t   MODES = MODES_M,
  // ISA
//isa_t        ISA = XLEN==32 ? '{spec: '{base: RV_32I , ext: XTEN}, priv: MODES}
//                 : XLEN==64 ? '{spec: '{base: RV_64I , ext: XTEN}, priv: MODES}
//                            : '{spec: '{base: RV_128I, ext: XTEN}, priv: MODES},
  isa_t ISA = '{spec: RV32I, priv: MODES_NONE},
`endif
  // instruction bus
  int unsigned IAW = 32,    // program address width
  int unsigned IDW = 32,    // program data    width
  int unsigned IBW = IDW/8, // program byte en width
  // data bus
  int unsigned DAW = 32,    // data    address width
  int unsigned DDW = XLEN,  // data    data    width
  int unsigned DBW = DDW/8, // data    byte en width
  // privilege implementation details
  logic [XLEN-1:0] PC0 = 'h0000_0000,   // reset vector
  // timing versus area compromises
  bit          CFG_BRU = 1'b0,  // enable dedicated BRanch Unit
  bit          CFG_BRA = 1'b1,  // enable dedicated BRanch Adder
  bit          CFG_LSA = 1'b0,  // enable dedicated Load/Store Adder
  // implementation device (ASIC/FPGA vendor/device)
  string       CHIP = ""
)(
  // system signals
  input  logic                  clk,
  input  logic                  rst,
  // program bus (instruction fetch)
  output logic                  if_vld,
  output logic [IAW-1:0]        if_adr,
  input  logic [IBW-1:0][8-1:0] if_rdt,
  input  logic                  if_rdy,
  // data bus (load/store)
  output logic                  ls_vld,  // write or read request
  output logic                  ls_wen,  // write enable
  output logic [DAW-1:0]        ls_adr,  // address
  output logic [DBW-1:0]        ls_ben,  // byte enable
  output logic [DBW-1:0][8-1:0] ls_wdt,  // write data
  input  logic [DBW-1:0][8-1:0] ls_rdt,  // read data
  input  logic                  ls_rdy   // write or read acknowledge
);

`ifdef SYNOPSYS_VERILOG_COMPILER
parameter isa_t ISA = '{spec: RV32I, priv: MODES_NONE};
`endif

///////////////////////////////////////////////////////////////////////////////
// local signals
///////////////////////////////////////////////////////////////////////////////

// instruction fetch
logic            if_run;  // running status
logic            if_tkn;  // taken
logic  [IAW-1:0] if_pc;   // program counter
logic  [IAW-1:0] if_pcn;  // program counter next
logic  [IAW-1:0] if_pcs;  // program counter sum
//logic  [IAW-1:0] if_pci;  // program counter incrementing adder
//logic  [IAW-1:0] if_pcb;  // program counter branch adder
logic            stall;

// instruction decode
ctl_t            id_ctl;  // control structure
logic            id_vld;  // instruction valid

// GPR read
logic [XLEN-1:0] gpr_rs1;  // register source 1
logic [XLEN-1:0] gpr_rs2;  // register source 2

// ALU
logic [XLEN-1:0] alu_dat;  // register destination
logic [XLEN-0:0] alu_sum;  // summation result including overflow bit

// MUL/DIV/REM
logic [XLEN-1:0] mul_dat;  // multiplier unit outpLENt

// CSR
logic [XLEN-1:0] csr_rdt;  // read  data

// CSR address map union
`ifdef VERILATOR
csr_map_ut       csr_csr;
`endif

logic [XLEN-1:0] csr_tvec;
logic [XLEN-1:0] csr_epc ;

// load/sore unit temporary signals
logic [XLEN-1:0] lsu_adr;  // address
logic [XLEN-1:0] lsu_wdt;  // write data
logic [XLEN-1:0] lsu_rdt;  // read data
logic            lsu_mal;  // MisALigned
logic            lsu_dly;  // DeLaYed writeback enable

// write back unit (GPR destination register access)
logic            wbu_wen;  // write enable
logic    [5-1:0] wbu_adr;  // address
logic [XLEN-1:0] wbu_dat;  // data

///////////////////////////////////////////////////////////////////////////////
// instruction fetch
///////////////////////////////////////////////////////////////////////////////

// start running after reset
always_ff @ (posedge clk, posedge rst)
if (rst)  if_run <= 1'b0;
else      if_run <= 1'b1;

// request becomes active after reset
assign if_vld = if_run & ~(ls_vld & ~ls_wen);

// PC next is used as IF address
assign if_adr = if_pcn;

// instruction valid
always_ff @ (posedge clk, posedge rst)
if (rst)  id_vld <= 1'b0;
else      id_vld <= (if_vld & if_rdy) | (id_vld & stall);

///////////////////////////////////////////////////////////////////////////////
// program counter
///////////////////////////////////////////////////////////////////////////////

// TODO:
assign stall = (if_vld & ~if_rdy) | (ls_vld & ~ls_rdy) | (ls_vld & ~ls_wen);

// program counter
always_ff @ (posedge clk, posedge rst)
if (rst)  if_pc <= IAW'(PC0);
else begin
  if (id_vld & ~stall) if_pc <= if_pcn;
end

generate
if (CFG_BRU) begin: gen_bru_ena

  // branch ALU for checking branch conditions
  r5p_bru #(
    .XLEN    (XLEN)
  ) br (
    // control
    .ctl     (id_ctl.i.bru),
    // data
    .rs1     (gpr_rs1),
    .rs2     (gpr_rs2),
    // status
    .tkn     (if_tkn)
  );

end: gen_bru_ena
else begin: gen_bru_alu

  always_comb
  case (id_ctl.i.bru)
    BEQ    : if_tkn = ~(|alu_sum[XLEN-1:0]);
    BNE    : if_tkn =  (|alu_sum[XLEN-1:0]);
    BLT    : if_tkn =    alu_sum[XLEN];
    BGE    : if_tkn = ~  alu_sum[XLEN];
    BLTU   : if_tkn =    alu_sum[XLEN];
    BGEU   : if_tkn = ~  alu_sum[XLEN];
    default: if_tkn = 'x;
  endcase

end: gen_bru_alu
endgenerate

// TODO: optimization parameters
// 1. branch immediate direct branch type decoder (kind of obvious, but see if it beats the tool optimizations)
// 2. separate adder for PC next and branch address, since mux control signal from ALU is late and is best used just before output
// 3. a separate branch ALU with explicit [un]signed comparator instead of adder in the main ALU
// 4. split PC adder into 12-bit immediate adder and the rest is an incrementer/decrementer, calculate both increment and decrement in advance.

generate
if (CFG_BRA) begin: gen_bra_add
  // simultaneous running adders, multiplexer with a late select signal
  // requires more adder logic improves timing
  logic [IAW-1:0] if_pci;  // PC incrementer
  logic [IAW-1:0] if_pcb;  // PC branch address adder

  // PC incrementer
  assign if_pci = if_pc + IAW'(id_ctl.siz);

  // branch address
  assign if_pcb = if_pc + IAW'(id_ctl.imm.b);

  // PC adder result multiplexer
  assign if_pcs = (id_ctl.i.pc == PC_BRN) & if_tkn ? if_pcb
                                                   : if_pci;

end: gen_bra_add
else begin: gen_bra_mux
  // the same adder is shared for next and branch address
  // least logic area
  logic [IAW-1:0] if_pca;  // PC addend

  // PC addend multiplexer
  assign if_pca = (id_ctl.i.pc == PC_BRN) & if_tkn ? IAW'(id_ctl.imm.b)
                                                   : IAW'(id_ctl.siz);

  // PC sum
  assign if_pcs = if_pc + if_pca;

end: gen_bra_mux
endgenerate

// program counter next
always_comb
if (if_rdy & id_vld) begin
  case (id_ctl.i.pc)
    PC_PCI,
    PC_BRN : if_pcn = if_pcs;
    PC_JMP : if_pcn = {alu_sum[IAW-1:1], 1'b0};
    PC_TRP : if_pcn = IAW'(csr_tvec);
    PC_EPC : if_pcn = IAW'(csr_epc);
    default: if_pcn = 'x;
  endcase
end else begin
  if_pcn = if_pc;
end

///////////////////////////////////////////////////////////////////////////////
// instruction decode
///////////////////////////////////////////////////////////////////////////////

`ifndef ALTERA_RESERVED_QIS
generate
if (ISA.spec.ext.C) begin: gen_d16

  import riscv_isa_c_pkg::*;

  // 16/32-bit instruction decoder
  always_comb
  case (opsiz(if_rdt[2-1:0]))
    2      : id_ctl = dec16(ISA, if_rdt[2-1:0]);  // 16-bit C standard extension
    4      : id_ctl = dec32(ISA, if_rdt[4-1:0]);  // 32-bit
    default: id_ctl = CTL_ILL;                    // OP sizes above 4 bytes are not supported
  endcase

end: gen_d16
else begin: gen_d32

  // 32-bit instruction decoder
  assign id_ctl = dec32(ISA, if_rdt[4-1:0]);

end: gen_d32
endgenerate
`else
// 32-bit instruction decoder
assign id_ctl = dec32(ISA, if_rdt[4-1:0]);
`endif

///////////////////////////////////////////////////////////////////////////////
// execute
///////////////////////////////////////////////////////////////////////////////

// general purpose registers
r5p_gpr #(
  .AW      (ISA.spec.base.E ? 4 : 5),
  .XLEN    (XLEN),
  .WBYP    (1'b1),
  .CHIP    (CHIP)
) gpr (
  // system signals
  .clk     (clk),
  .rst     (rst),
  // read/write enable
  .e_rs1   (id_ctl.gpr.e.rs1),
  .e_rs2   (id_ctl.gpr.e.rs2),
  .e_rd    (wbu_wen),
  // read/write address
  .a_rs1   (id_ctl.gpr.a.rs1),
  .a_rs2   (id_ctl.gpr.a.rs2),
  .a_rd    (wbu_adr),
  // read/write data
  .d_rs1   (gpr_rs1),
  .d_rs2   (gpr_rs2),
  .d_rd    (wbu_dat)
);

// base ALU
r5p_alu #(
  .XLEN    (XLEN),
  .CFG_LSA (CFG_LSA)
) alu (
   // system signals
  .clk     (clk),
  .rst     (rst),
  // control
  .ctl     (id_ctl),
  // data input/output
  .pc      (XLEN'(if_pc)),
  .rs1     (gpr_rs1),
  .rs2     (gpr_rs2),
  .rd      (alu_dat),
  // side ouputs
  .sum     (alu_sum)
);

`ifndef ALTERA_RESERVED_QIS
generate
if (ISA.spec.ext.M == 1'b1) begin: gen_mdu

  // mul/div/rem unit
  r5p_mdu #(
    .XLEN    (XLEN)
  ) mdu (
    // system signals
    .clk     (clk),
    .rst     (rst),
    // control
    .ctl     (id_ctl.m),
    // data input/output
    .rs1     (gpr_rs1),
    .rs2     (gpr_rs2),
    .rd      (mul_dat)
  );

end: gen_mdu
else begin: gen_nomdu

  // data output
  assign mul_dat = 'x;

end: gen_nomdu
endgenerate
`endif

///////////////////////////////////////////////////////////////////////////////
// CSR
///////////////////////////////////////////////////////////////////////////////

//`ifndef ALTERA_RESERVED_QIS
//generate
//if (ISA.spec.ext.Zicsr) begin: gen_csr_ena
//
//  r5p_csr #(
//    .XLEN    (XLEN)
//  ) csr (
//    // system signals
//    .clk     (clk),
//    .rst     (rst),
//    // CSR address map union output
//    .csr_map (csr_csr),
//    // CSR control and data input/output
//    .csr_ctl (id_ctl.csr),
//    .csr_wdt (gpr_rs1),
//    .csr_rdt (csr_rdt),
//    // trap handler
//    .priv_i  (id_ctl.priv),
//    .trap_i  (id_ctl.i.pc == PC_TRP),
//  //.cause_i (CAUSE_EXC_OP_EBREAK),
//    .epc_i   (XLEN'(if_pc)),
//    .epc_o   (csr_epc ),
//    .tvec_o  (csr_tvec),
//    // hardware performance monitor
//    .event_i (r5p_hpmevent_t'(1))
//    // TODO: debugger, ...
//  );
//
//end: gen_csr_ena
//else begin: gen_csr_byp

  // CSR data output
  assign csr_rdt  = 'x;
  // trap handler
  assign csr_epc  = 'x;
  assign csr_tvec = 'x;

//end: gen_csr_byp
//endgenerate
//`endif

///////////////////////////////////////////////////////////////////////////////
// load/store
///////////////////////////////////////////////////////////////////////////////

generate
if (CFG_LSA) begin: gen_lsa_ena

  logic [XLEN-1:0] lsu_adr_ld;  // address load
  logic [XLEN-1:0] lsu_adr_st;  // address store

  // dedicated load/store adders
  assign lsu_adr_ld = gpr_rs1 + XLEN'(id_ctl.imm.l);  // I-type (load)
  assign lsu_adr_st = gpr_rs1 + XLEN'(id_ctl.imm.s);  // S-type (store)

  always_comb
  unique casez (id_ctl.i.alu.ai)
    AI_R1_IL: lsu_adr = lsu_adr_ld;  // I-type (load)
    AI_R1_IS: lsu_adr = lsu_adr_st;  // S-type (store)
    default : lsu_adr = 'x ;
  endcase

end:gen_lsa_ena
else begin: gen_lsa_alu

  // ALU is used to calculate load/store address
  assign lsu_adr = alu_sum[XLEN-1:0];

end: gen_lsa_alu
endgenerate

// intermediate signals
assign lsu_wdt = gpr_rs2;

// load/store unit
r5p_lsu #(
  .XLEN    (XLEN),
  // data bus
  .AW      (DAW),
  .DW      (DDW),
  .BW      (DBW)
) lsu (
  // system signals
  .clk     (clk),
  .rst     (rst),
  // control
  .ctl     (id_ctl.i.lsu),
  // data input/output
  .adr     (lsu_adr),
  .wdt     (lsu_wdt),
  .rdt     (lsu_rdt),
  .mal     (lsu_mal),
  .dly     (lsu_dly),
  // data bus (load/store)
  .ls_vld  (ls_vld),
  .ls_wen  (ls_wen),
  .ls_adr  (ls_adr),
  .ls_ben  (ls_ben),
  .ls_wdt  (ls_wdt),
  .ls_rdt  (ls_rdt),
  .ls_rdy  (ls_rdy)
);

///////////////////////////////////////////////////////////////////////////////
// write back
///////////////////////////////////////////////////////////////////////////////

r5p_wbu #(
  .XLEN    (XLEN)
) wbu (
  // system signals
  .clk     (clk),
  .rst     (rst),
  // control
  .ctl     (id_ctl),
  // write data inputs
  .alu     (alu_dat),              // ALU output
  .lsu     (lsu_rdt),              // LSU load
  .pcs     (XLEN'(if_pcs)),        // PC increment
  .imm     (XLEN'(id_ctl.imm.u)),  // immediate
  .csr     (csr_rdt),              // CSR
  .mul     (mul_dat),              // mul/div/rem
  // GPR write back
  .wen     (wbu_wen),
  .adr     (wbu_adr),
  .dat     (wbu_dat)
);

endmodule: r5p_core
