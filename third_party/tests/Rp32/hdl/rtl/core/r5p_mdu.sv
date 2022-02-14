///////////////////////////////////////////////////////////////////////////////
// R5P: multiply/divide unit
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

module r5p_mdu #(
  int unsigned XLEN = 32
)(
  // system signals
  input  logic            clk,  // clock
  input  logic            rst,  // reset
  // control
  input  ctl_m_t          ctl,
  // data input/output
  input  logic [XLEN-1:0] rs1,  // source register 1
  input  logic [XLEN-1:0] rs2,  // source register 2
  output logic [XLEN-1:0] rd    // destination register
);

// minux max (most negative value)
localparam logic [XLEN-1:0] M8 = {1'b1, {XLEN-1{1'b0}}};
// minus 1 (-1)
localparam logic [XLEN-1:0] M1 = '1;

logic          [2-1:0][XLEN-1:0] mul;
logic unsigned        [XLEN-1:0] divu;
logic   signed        [XLEN-1:0] divs;
logic                 [XLEN-1:0] div;
logic unsigned        [XLEN-1:0] remu;
logic   signed        [XLEN-1:0] rems;
logic                 [XLEN-1:0] rem;

// NOTE:
// for signed*unsigned multiplication to work in Verilog,
// the first operand must be sign extended to the LHS (result) width

// multiplication
always_comb
case (ctl.s12) inside
  2'b00  : mul = 64'($unsigned(rs1)) * $unsigned(rs2);
  2'b10  : mul = 64'(  $signed(rs1)) * $unsigned(rs2);
  2'b11  : mul = 64'(  $signed(rs1)) *   $signed(rs2);
  default: mul = 'x;
endcase

// NOTE:
// for signed/signed division to work in Verilog,
// the LHS (result) must also be a signed signal,
// for the sema reason divide by zero and overflow conditions are in a separete equation

// division
always_comb
begin
divu = $unsigned(rs1) / $unsigned(rs2);
divs =   $signed(rs1) /   $signed(rs2);
case (ctl.s12) inside
  2'b00  : div = ~|rs2 ?  '1 :                            divu;
  2'b11  : div = ~|rs2 ?  '1 : (rs1==M8 & rs2==M1) ? M8 : divs;
  default: div = 'x;
endcase
end

// NOTE:
// same as for the divider

// reminder
always_comb
begin
remu = $unsigned(rs1) % $unsigned(rs2);
rems =   $signed(rs1) %   $signed(rs2);
case (ctl.s12) inside
  2'b00  : rem = ~|rs2 ? rs1 :                            remu;
  2'b11  : rem = ~|rs2 ? rs1 : (rs1==M8 & rs2==M1) ? '0 : rems;
  default: rem = 'x;
endcase
end

always_comb
case (ctl.op) inside
  M_MUL: rd = mul[0];
  M_MUH: rd = mul[1];
  M_DIV: rd = div;
  M_REM: rd = rem;
endcase

logic unsigned [2*XLEN-1:0] mul64u;
logic   signed [2*XLEN-1:0] mul64s;

assign mul64u =   $signed(rs1) * $unsigned(rs2);
assign mul64s =   $signed(rs1) * $unsigned(rs2);

endmodule: r5p_mdu