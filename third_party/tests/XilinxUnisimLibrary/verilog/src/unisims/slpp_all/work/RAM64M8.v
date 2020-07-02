///////////////////////////////////////////////////////////////////////////////
//     Copyright (c) 1995/2014 Xilinx, Inc.
// 
//    Licensed under the Apache License, Version 2.0 (the "License");
//    you may not use this file except in compliance with the License.
//    You may obtain a copy of the License at
// 
//        http://www.apache.org/licenses/LICENSE-2.0
// 
//    Unless required by applicable law or agreed to in writing, software
//    distributed under the License is distributed on an "AS IS" BASIS,
//    WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
//    See the License for the specific language governing permissions and
//    limitations under the License.
///////////////////////////////////////////////////////////////////////////////
//   ____  ____
//  /   /\/   /
// /___/  \  /     Vendor      : Xilinx
// \   \   \/      Version     : 2014.3
//  \   \          Description : Xilinx Timing Simulation Library Component
//  /   /                        64-Deep by 8-bit Wide Multi Port RAM
// /___/   /\      Filename    : RAM64M8.v
// \   \  /  \
//  \___\/\___\
//
///////////////////////////////////////////////////////////////////////////////
// Revision:
//    07/02/12 - Initial version, from RAM64M
//    09/17/12 - 678604 - fix compilation errors
//    10/22/14 - Added #1 to $finish (CR 808642).
// End Revision:
///////////////////////////////////////////////////////////////////////////////

`timescale 1 ps / 1 ps

`celldefine

module RAM64M8 #(



  parameter [63:0] INIT_A = 64'h0000000000000000,
  parameter [63:0] INIT_B = 64'h0000000000000000,
  parameter [63:0] INIT_C = 64'h0000000000000000,
  parameter [63:0] INIT_D = 64'h0000000000000000,
  parameter [63:0] INIT_E = 64'h0000000000000000,
  parameter [63:0] INIT_F = 64'h0000000000000000,
  parameter [63:0] INIT_G = 64'h0000000000000000,
  parameter [63:0] INIT_H = 64'h0000000000000000,
  parameter [0:0] IS_WCLK_INVERTED = 1'b0
)(
  output DOA,
  output DOB,
  output DOC,
  output DOD,
  output DOE,
  output DOF,
  output DOG,
  output DOH,

  input [5:0] ADDRA,
  input [5:0] ADDRB,
  input [5:0] ADDRC,
  input [5:0] ADDRD,
  input [5:0] ADDRE,
  input [5:0] ADDRF,
  input [5:0] ADDRG,
  input [5:0] ADDRH,
  input DIA,
  input DIB,
  input DIC,
  input DID,
  input DIE,
  input DIF,
  input DIG,
  input DIH,
  input WCLK,
  input WE
);
  
// define constants
  localparam MODULE_NAME = "RAM64M8";

  reg trig_attr = 1'b0;




  reg attr_test = 1'b0;

  reg attr_err = 1'b0;

  wire IS_WCLK_INVERTED_BIN;

  wire [5:0] ADDRH_in;
  wire DIA_in;
  wire DIB_in;
  wire DIC_in;
  wire DID_in;
  wire DIE_in;
  wire DIF_in;
  wire DIG_in;
  wire DIH_in;
  wire WCLK_in;
  wire WE_in;
































  assign ADDRH_in = ADDRH;
  assign DIA_in = DIA;
  assign DIB_in = DIB;
  assign DIC_in = DIC;
  assign DID_in = DID;
  assign DIE_in = DIE;
  assign DIF_in = DIF;
  assign DIG_in = DIG;
  assign DIH_in = DIH;
  assign WCLK_in = WCLK ^ IS_WCLK_INVERTED_BIN;
  assign WE_in = (WE === 1'bz) || WE; // rv 1


  assign IS_WCLK_INVERTED_BIN = IS_WCLK_INVERTED;

  reg [63:0] mem_a, mem_b, mem_c, mem_d;
  reg [63:0] mem_e, mem_f, mem_g, mem_h;

  initial begin
    mem_a = INIT_A;
    mem_b = INIT_B;
    mem_c = INIT_C;
    mem_d = INIT_D;
    mem_e = INIT_E;
    mem_f = INIT_F;
    mem_g = INIT_G;
    mem_h = INIT_H;
  end

  always @(posedge WCLK_in)
    if (WE_in) begin
      mem_a[ADDRH_in] <= #100 DIA_in;
      mem_b[ADDRH_in] <= #100 DIB_in;
      mem_c[ADDRH_in] <= #100 DIC_in;
      mem_d[ADDRH_in] <= #100 DID_in;
      mem_e[ADDRH_in] <= #100 DIE_in;
      mem_f[ADDRH_in] <= #100 DIF_in;
      mem_g[ADDRH_in] <= #100 DIG_in;
      mem_h[ADDRH_in] <= #100 DIH_in;
  end

   assign  DOA = mem_a[ADDRA];
   assign  DOB = mem_b[ADDRB];
   assign  DOC = mem_c[ADDRC];
   assign  DOD = mem_d[ADDRD];
   assign  DOE = mem_e[ADDRE];
   assign  DOF = mem_f[ADDRF];
   assign  DOG = mem_g[ADDRG];
   assign  DOH = mem_h[ADDRH_in];





































































































endmodule

`endcelldefine
