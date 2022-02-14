///////////////////////////////////////////////////////////////////////////////
// R5P: branch unit
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

module r5p_bru #(
  int unsigned XLEN = 32
)(
  // control
  input  bru_t            ctl,
  // data input/output
  input  logic [XLEN-1:0] rs1,  // source register 1
  input  logic [XLEN-1:0] rs2,  // source register 2
  // status
  output logic            tkn   // taken
);

logic eq;   // equal
logic lt;   // less then
logic lts;  // less then   signed
logic ltu;  // less then unsigned

assign eq  = rs1          == rs2          ;  // equal
assign lt  = rs1[XLEN-2:0] < rs2[XLEN-2:0];  // less then

assign lts = (rs1[XLEN-1] == rs2[XLEN-1]) ? lt : (rs1[XLEN-1] > rs2[XLEN-1]);  // less then   signed
assign ltu = (rs1[XLEN-1] == rs2[XLEN-1]) ? lt : (rs1[XLEN-1] < rs2[XLEN-1]);  // less then unsigned

always_comb
case (ctl)
  BEQ    : tkn =  eq ;
  BNE    : tkn = ~eq ;
  BLT    : tkn =  lts;
  BGE    : tkn = ~lts;
  BLTU   : tkn =  ltu;
  BGEU   : tkn = ~ltu;
  default: tkn = 'x;
endcase

endmodule: r5p_bru