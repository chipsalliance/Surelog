///////////////////////////////////////////////////////////////////////////////
// R5P: write back unit
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

module r5p_wbu #(
  int unsigned XLEN = 32  // XLEN width
)(
  // system signals
  input  logic            clk,  // clock
  input  logic            rst,  // reset
  // control structure
  input  ctl_t            ctl,
  // write data inputs
  input  logic [XLEN-1:0] alu,
  input  logic [XLEN-1:0] lsu,
  input  logic [XLEN-1:0] pcs,
  input  logic [XLEN-1:0] imm,
  input  logic [XLEN-1:0] csr,
  input  logic [XLEN-1:0] mul,
  // GPR write back
  output logic            wen,  // write enable
  output logic [5-1:0]    adr,  // GPR address
  output logic [XLEN-1:0] dat   // data
);

// write data inputs
logic [XLEN-1:0] tmp_alu;
logic [XLEN-1:0] tmp_lsu;
logic [XLEN-1:0] tmp_pcs;
logic [XLEN-1:0] tmp_imm;
logic [XLEN-1:0] tmp_csr;
logic [XLEN-1:0] tmp_mul;
logic [XLEN-1:0] tmp;

// multiplexer select
wbu_t sel;

// destination register write enable and address
always_ff @(posedge clk, posedge rst)
if (rst) begin
  wen <= 1'b0;
  adr <= 5'd0;
  sel <= WB_IDL;  // TODO: there might be a better choice
end else begin
  wen <= ctl.gpr.e.rd;
  adr <= ctl.gpr.a.rd;
  sel <= ctl.i.wbu;
end

// pre multiplexer
always_ff @(posedge clk, posedge rst)
if (rst) begin
  tmp <= '0;
end else begin
  unique case (ctl.i.wbu)
    WB_ALU : tmp <= alu;  // ALU output
    WB_LSU : tmp <=  'x;  // LSU load data
    WB_PCI : tmp <= pcs;  // PC increment
    WB_IMM : tmp <= imm;  // immediate
    WB_CSR : tmp <= csr;  // CSR
    WB_MUL : tmp <= mul;  // mul/div/rem
    default: tmp <=  'x;  // none
  endcase
end

// write back multiplexer
always_comb begin
  unique case (sel)
    WB_ALU : dat = tmp;  // ALU output
    WB_LSU : dat = lsu;  // LSU load data
    WB_PCI : dat = tmp;  // PC increment
    WB_IMM : dat = tmp;  // immediate
    WB_CSR : dat = tmp;  // CSR
    WB_MUL : dat = tmp;  // mul/div/rem
    default: dat = 'x;   // none
  endcase
end

endmodule: r5p_wbu