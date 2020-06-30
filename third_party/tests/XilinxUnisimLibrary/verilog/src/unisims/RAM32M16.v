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
// /___/  \  /    Vendor      : Xilinx
// \   \   \/     Version     : 2014.3
//  \   \         Description : Xilinx Unified Simulation Library Component
//  /   /                       32-Deep by 16-bit Wide Multi Port RAM 
// /___/   /\     Filename    : RAM32M16.v
// \   \  /  \
//  \___\/\___\
//
///////////////////////////////////////////////////////////////////////////////
//  Revision:
//    07/02/12 - Initial version, from RAM32M
//    10/22/14 - Added #1 to $finish (CR 808642).
//  End Revision:
///////////////////////////////////////////////////////////////////////////////

`timescale 1 ps / 1 ps

`celldefine

module RAM32M16 #(
`ifdef XIL_TIMING
  parameter LOC = "UNPLACED",
`endif
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
  output [1:0] DOA,
  output [1:0] DOB,
  output [1:0] DOC,
  output [1:0] DOD,
  output [1:0] DOE,
  output [1:0] DOF,
  output [1:0] DOG,
  output [1:0] DOH,

  input [4:0] ADDRA,
  input [4:0] ADDRB,
  input [4:0] ADDRC,
  input [4:0] ADDRD,
  input [4:0] ADDRE,
  input [4:0] ADDRF,
  input [4:0] ADDRG,
  input [4:0] ADDRH,
  input [1:0] DIA,
  input [1:0] DIB,
  input [1:0] DIC,
  input [1:0] DID,
  input [1:0] DIE,
  input [1:0] DIF,
  input [1:0] DIG,
  input [1:0] DIH,
  input WCLK,
  input WE
);
  
// define constants
  localparam MODULE_NAME = "RAM32M16";

  reg trig_attr = 1'b0;

`ifdef XIL_ATTR_TEST
  reg attr_test = 1'b1;
`else
  reg attr_test = 1'b0;
`endif
  reg attr_err = 1'b0;

  wire IS_WCLK_INVERTED_BIN;

  wire [4:0] ADDRH_in;
  wire [1:0] DIA_in;
  wire [1:0] DIB_in;
  wire [1:0] DIC_in;
  wire [1:0] DID_in;
  wire [1:0] DIE_in;
  wire [1:0] DIF_in;
  wire [1:0] DIG_in;
  wire [1:0] DIH_in;
  wire WCLK_in;
  wire WE_in;

`ifdef XIL_TIMING
  wire [4:0] ADDRH_dly;
  wire [1:0] DIA_dly;
  wire [1:0] DIB_dly;
  wire [1:0] DIC_dly;
  wire [1:0] DID_dly;
  wire [1:0] DIE_dly;
  wire [1:0] DIF_dly;
  wire [1:0] DIG_dly;
  wire [1:0] DIH_dly;
  wire WCLK_dly;
  wire WE_dly;

  reg notifier;

  wire sh_clk_en_p;
  wire sh_clk_en_n;
  wire sh_we_clk_en_p;
  wire sh_we_clk_en_n;

  assign ADDRH_in = ADDRH_dly;
  assign DIA_in = DIA_dly;
  assign DIB_in = DIB_dly;
  assign DIC_in = DIC_dly;
  assign DID_in = DID_dly;
  assign DIE_in = DIE_dly;
  assign DIF_in = DIF_dly;
  assign DIG_in = DIG_dly;
  assign DIH_in = DIH_dly;
  assign WCLK_in = WCLK_dly ^ IS_WCLK_INVERTED_BIN;
  assign WE_in = (WE === 1'bz) || WE_dly; // rv 1
`else
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
`endif
    
  assign IS_WCLK_INVERTED_BIN = IS_WCLK_INVERTED;

  reg [63:0] mem_a, mem_b, mem_c, mem_d;
  reg [63:0] mem_e, mem_f, mem_g, mem_h;
  reg [5:0] addr_in2, addr_in1;

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

  always @(ADDRH_in) begin
      addr_in2 = 2 * ADDRH_in;
      addr_in1 = 2 * ADDRH_in + 1;
  end

  always @(posedge WCLK_in)
    if (WE_in) begin
      mem_a[addr_in2] <= #100 DIA_in[0];
      mem_a[addr_in1] <= #100 DIA_in[1];
      mem_b[addr_in2] <= #100 DIB_in[0];
      mem_b[addr_in1] <= #100 DIB_in[1];
      mem_c[addr_in2] <= #100 DIC_in[0];
      mem_c[addr_in1] <= #100 DIC_in[1];
      mem_d[addr_in2] <= #100 DID_in[0];
      mem_d[addr_in1] <= #100 DID_in[1];
      mem_e[addr_in2] <= #100 DIE_in[0];
      mem_e[addr_in1] <= #100 DIE_in[1];
      mem_f[addr_in2] <= #100 DIF_in[0];
      mem_f[addr_in1] <= #100 DIF_in[1];
      mem_g[addr_in2] <= #100 DIG_in[0];
      mem_g[addr_in1] <= #100 DIG_in[1];
      mem_h[addr_in2] <= #100 DIH_in[0];
      mem_h[addr_in1] <= #100 DIH_in[1];
  end

   assign  DOA[0] = mem_a[2*ADDRA];
   assign  DOA[1] = mem_a[2*ADDRA + 1];
   assign  DOB[0] = mem_b[2*ADDRB];
   assign  DOB[1] = mem_b[2*ADDRB + 1];
   assign  DOC[0] = mem_c[2*ADDRC];
   assign  DOC[1] = mem_c[2*ADDRC + 1];
   assign  DOD[0] = mem_d[2*ADDRD];
   assign  DOD[1] = mem_d[2*ADDRD + 1];
   assign  DOE[0] = mem_e[2*ADDRE];
   assign  DOE[1] = mem_e[2*ADDRE + 1];
   assign  DOF[0] = mem_f[2*ADDRF];
   assign  DOF[1] = mem_f[2*ADDRF + 1];
   assign  DOG[0] = mem_g[2*ADDRG];
   assign  DOG[1] = mem_g[2*ADDRG + 1];
   assign  DOH[0] = mem_h[2*ADDRH_in];
   assign  DOH[1] = mem_h[2*ADDRH_in + 1];

`ifdef XIL_TIMING
  always @(notifier) begin
      mem_a[addr_in2] <= 1'bx;
      mem_a[addr_in1] <= 1'bx;
      mem_b[addr_in2] <= 1'bx;
      mem_b[addr_in1] <= 1'bx;
      mem_c[addr_in2] <= 1'bx;
      mem_c[addr_in1] <= 1'bx;
      mem_d[addr_in2] <= 1'bx;
      mem_d[addr_in1] <= 1'bx;
      mem_e[addr_in2] <= 1'bx;
      mem_e[addr_in1] <= 1'bx;
      mem_f[addr_in2] <= 1'bx;
      mem_f[addr_in1] <= 1'bx;
      mem_g[addr_in2] <= 1'bx;
      mem_g[addr_in1] <= 1'bx;
      mem_h[addr_in2] <= 1'bx;
      mem_h[addr_in1] <= 1'bx;
  end

  assign sh_clk_en_p = ~IS_WCLK_INVERTED_BIN;
  assign sh_clk_en_n = IS_WCLK_INVERTED_BIN;
  assign sh_we_clk_en_p = WE_in && ~IS_WCLK_INVERTED_BIN;
  assign sh_we_clk_en_n = WE_in && IS_WCLK_INVERTED_BIN;

  specify
  (WCLK => DOA[0]) = (0:0:0, 0:0:0);
  (WCLK => DOA[1]) = (0:0:0, 0:0:0);
  (WCLK => DOB[0]) = (0:0:0, 0:0:0);
  (WCLK => DOB[1]) = (0:0:0, 0:0:0);
  (WCLK => DOC[0]) = (0:0:0, 0:0:0);
  (WCLK => DOC[1]) = (0:0:0, 0:0:0);
  (WCLK => DOD[0]) = (0:0:0, 0:0:0);
  (WCLK => DOD[1]) = (0:0:0, 0:0:0);
  (WCLK => DOE[0]) = (0:0:0, 0:0:0);
  (WCLK => DOE[1]) = (0:0:0, 0:0:0);
  (WCLK => DOF[0]) = (0:0:0, 0:0:0);
  (WCLK => DOF[1]) = (0:0:0, 0:0:0);
  (WCLK => DOG[0]) = (0:0:0, 0:0:0);
  (WCLK => DOG[1]) = (0:0:0, 0:0:0);
  (WCLK => DOH[0]) = (0:0:0, 0:0:0);
  (WCLK => DOH[1]) = (0:0:0, 0:0:0);
  (ADDRA *> DOA[0]) = (0:0:0, 0:0:0);
  (ADDRA *> DOA[1]) = (0:0:0, 0:0:0);
  (ADDRB *> DOB[0]) = (0:0:0, 0:0:0);
  (ADDRB *> DOB[1]) = (0:0:0, 0:0:0);
  (ADDRC *> DOC[0]) = (0:0:0, 0:0:0);
  (ADDRC *> DOC[1]) = (0:0:0, 0:0:0);
  (ADDRD *> DOD[0]) = (0:0:0, 0:0:0);
  (ADDRD *> DOD[1]) = (0:0:0, 0:0:0);
  (ADDRE *> DOE[0]) = (0:0:0, 0:0:0);
  (ADDRE *> DOE[1]) = (0:0:0, 0:0:0);
  (ADDRF *> DOF[0]) = (0:0:0, 0:0:0);
  (ADDRF *> DOF[1]) = (0:0:0, 0:0:0);
  (ADDRG *> DOG[0]) = (0:0:0, 0:0:0);
  (ADDRG *> DOG[1]) = (0:0:0, 0:0:0);
  (ADDRH *> DOH[0]) = (0:0:0, 0:0:0);
  (ADDRH *> DOH[1]) = (0:0:0, 0:0:0);
  $period (negedge WCLK &&& WE, 0:0:0, notifier);
  $period (posedge WCLK &&& WE, 0:0:0, notifier);
  $setuphold (negedge WCLK, negedge ADDRH[0], 0:0:0, 0:0:0, notifier,sh_we_clk_en_n,sh_we_clk_en_n,WCLK_dly,ADDRH_dly[0]);
  $setuphold (negedge WCLK, negedge ADDRH[1], 0:0:0, 0:0:0, notifier,sh_we_clk_en_n,sh_we_clk_en_n,WCLK_dly,ADDRH_dly[1]);
  $setuphold (negedge WCLK, negedge ADDRH[2], 0:0:0, 0:0:0, notifier,sh_we_clk_en_n,sh_we_clk_en_n,WCLK_dly,ADDRH_dly[2]);
  $setuphold (negedge WCLK, negedge ADDRH[3], 0:0:0, 0:0:0, notifier,sh_we_clk_en_n,sh_we_clk_en_n,WCLK_dly,ADDRH_dly[3]);
  $setuphold (negedge WCLK, negedge ADDRH[4], 0:0:0, 0:0:0, notifier,sh_we_clk_en_n,sh_we_clk_en_n,WCLK_dly,ADDRH_dly[4]);
  $setuphold (negedge WCLK, negedge DIA[0], 0:0:0, 0:0:0, notifier,sh_we_clk_en_n,sh_we_clk_en_n,WCLK_dly,DIA_dly[0]);
  $setuphold (negedge WCLK, negedge DIA[1], 0:0:0, 0:0:0, notifier,sh_we_clk_en_n,sh_we_clk_en_n,WCLK_dly,DIA_dly[1]);
  $setuphold (negedge WCLK, negedge DIB[0], 0:0:0, 0:0:0, notifier,sh_we_clk_en_n,sh_we_clk_en_n,WCLK_dly,DIB_dly[0]);
  $setuphold (negedge WCLK, negedge DIB[1], 0:0:0, 0:0:0, notifier,sh_we_clk_en_n,sh_we_clk_en_n,WCLK_dly,DIB_dly[1]);
  $setuphold (negedge WCLK, negedge DIC[0], 0:0:0, 0:0:0, notifier,sh_we_clk_en_n,sh_we_clk_en_n,WCLK_dly,DIC_dly[0]);
  $setuphold (negedge WCLK, negedge DIC[1], 0:0:0, 0:0:0, notifier,sh_we_clk_en_n,sh_we_clk_en_n,WCLK_dly,DIC_dly[1]);
  $setuphold (negedge WCLK, negedge DID[0], 0:0:0, 0:0:0, notifier,sh_we_clk_en_n,sh_we_clk_en_n,WCLK_dly,DID_dly[0]);
  $setuphold (negedge WCLK, negedge DID[1], 0:0:0, 0:0:0, notifier,sh_we_clk_en_n,sh_we_clk_en_n,WCLK_dly,DID_dly[1]);
  $setuphold (negedge WCLK, negedge DIE[0], 0:0:0, 0:0:0, notifier,sh_we_clk_en_n,sh_we_clk_en_n,WCLK_dly,DIE_dly[0]);
  $setuphold (negedge WCLK, negedge DIE[1], 0:0:0, 0:0:0, notifier,sh_we_clk_en_n,sh_we_clk_en_n,WCLK_dly,DIE_dly[1]);
  $setuphold (negedge WCLK, negedge DIF[0], 0:0:0, 0:0:0, notifier,sh_we_clk_en_n,sh_we_clk_en_n,WCLK_dly,DIF_dly[0]);
  $setuphold (negedge WCLK, negedge DIF[1], 0:0:0, 0:0:0, notifier,sh_we_clk_en_n,sh_we_clk_en_n,WCLK_dly,DIF_dly[1]);
  $setuphold (negedge WCLK, negedge DIG[0], 0:0:0, 0:0:0, notifier,sh_we_clk_en_n,sh_we_clk_en_n,WCLK_dly,DIG_dly[0]);
  $setuphold (negedge WCLK, negedge DIG[1], 0:0:0, 0:0:0, notifier,sh_we_clk_en_n,sh_we_clk_en_n,WCLK_dly,DIG_dly[1]);
  $setuphold (negedge WCLK, negedge DIH[0], 0:0:0, 0:0:0, notifier,sh_we_clk_en_n,sh_we_clk_en_n,WCLK_dly,DIH_dly[0]);
  $setuphold (negedge WCLK, negedge DIH[1], 0:0:0, 0:0:0, notifier,sh_we_clk_en_n,sh_we_clk_en_n,WCLK_dly,DIH_dly[1]);
  $setuphold (negedge WCLK, negedge WE, 0:0:0, 0:0:0, notifier,sh_clk_en_n,sh_clk_en_n,WCLK_dly,WE_dly);
  $setuphold (negedge WCLK, posedge ADDRH[0], 0:0:0, 0:0:0, notifier,sh_we_clk_en_n,sh_we_clk_en_n,WCLK_dly,ADDRH_dly[0]);
  $setuphold (negedge WCLK, posedge ADDRH[1], 0:0:0, 0:0:0, notifier,sh_we_clk_en_n,sh_we_clk_en_n,WCLK_dly,ADDRH_dly[1]);
  $setuphold (negedge WCLK, posedge ADDRH[2], 0:0:0, 0:0:0, notifier,sh_we_clk_en_n,sh_we_clk_en_n,WCLK_dly,ADDRH_dly[2]);
  $setuphold (negedge WCLK, posedge ADDRH[3], 0:0:0, 0:0:0, notifier,sh_we_clk_en_n,sh_we_clk_en_n,WCLK_dly,ADDRH_dly[3]);
  $setuphold (negedge WCLK, posedge ADDRH[4], 0:0:0, 0:0:0, notifier,sh_we_clk_en_n,sh_we_clk_en_n,WCLK_dly,ADDRH_dly[4]);
  $setuphold (negedge WCLK, posedge DIA[0], 0:0:0, 0:0:0, notifier,sh_we_clk_en_n,sh_we_clk_en_n,WCLK_dly,DIA_dly[0]);
  $setuphold (negedge WCLK, posedge DIA[1], 0:0:0, 0:0:0, notifier,sh_we_clk_en_n,sh_we_clk_en_n,WCLK_dly,DIA_dly[1]);
  $setuphold (negedge WCLK, posedge DIB[0], 0:0:0, 0:0:0, notifier,sh_we_clk_en_n,sh_we_clk_en_n,WCLK_dly,DIB_dly[0]);
  $setuphold (negedge WCLK, posedge DIB[1], 0:0:0, 0:0:0, notifier,sh_we_clk_en_n,sh_we_clk_en_n,WCLK_dly,DIB_dly[1]);
  $setuphold (negedge WCLK, posedge DIC[0], 0:0:0, 0:0:0, notifier,sh_we_clk_en_n,sh_we_clk_en_n,WCLK_dly,DIC_dly[0]);
  $setuphold (negedge WCLK, posedge DIC[1], 0:0:0, 0:0:0, notifier,sh_we_clk_en_n,sh_we_clk_en_n,WCLK_dly,DIC_dly[1]);
  $setuphold (negedge WCLK, posedge DID[0], 0:0:0, 0:0:0, notifier,sh_we_clk_en_n,sh_we_clk_en_n,WCLK_dly,DID_dly[0]);
  $setuphold (negedge WCLK, posedge DID[1], 0:0:0, 0:0:0, notifier,sh_we_clk_en_n,sh_we_clk_en_n,WCLK_dly,DID_dly[1]);
  $setuphold (negedge WCLK, posedge DIE[0], 0:0:0, 0:0:0, notifier,sh_we_clk_en_n,sh_we_clk_en_n,WCLK_dly,DIE_dly[0]);
  $setuphold (negedge WCLK, posedge DIE[1], 0:0:0, 0:0:0, notifier,sh_we_clk_en_n,sh_we_clk_en_n,WCLK_dly,DIE_dly[1]);
  $setuphold (negedge WCLK, posedge DIF[0], 0:0:0, 0:0:0, notifier,sh_we_clk_en_n,sh_we_clk_en_n,WCLK_dly,DIF_dly[0]);
  $setuphold (negedge WCLK, posedge DIF[1], 0:0:0, 0:0:0, notifier,sh_we_clk_en_n,sh_we_clk_en_n,WCLK_dly,DIF_dly[1]);
  $setuphold (negedge WCLK, posedge DIG[0], 0:0:0, 0:0:0, notifier,sh_we_clk_en_n,sh_we_clk_en_n,WCLK_dly,DIG_dly[0]);
  $setuphold (negedge WCLK, posedge DIG[1], 0:0:0, 0:0:0, notifier,sh_we_clk_en_n,sh_we_clk_en_n,WCLK_dly,DIG_dly[1]);
  $setuphold (negedge WCLK, posedge DIH[0], 0:0:0, 0:0:0, notifier,sh_we_clk_en_n,sh_we_clk_en_n,WCLK_dly,DIH_dly[0]);
  $setuphold (negedge WCLK, posedge DIH[1], 0:0:0, 0:0:0, notifier,sh_we_clk_en_n,sh_we_clk_en_n,WCLK_dly,DIH_dly[1]);
  $setuphold (negedge WCLK, posedge WE, 0:0:0, 0:0:0, notifier,sh_clk_en_n,sh_clk_en_n,WCLK_dly,WE_dly);
  $setuphold (posedge WCLK, negedge ADDRH[0], 0:0:0, 0:0:0, notifier,sh_we_clk_en_p,sh_we_clk_en_p,WCLK_dly,ADDRH_dly[0]);
  $setuphold (posedge WCLK, negedge ADDRH[1], 0:0:0, 0:0:0, notifier,sh_we_clk_en_p,sh_we_clk_en_p,WCLK_dly,ADDRH_dly[1]);
  $setuphold (posedge WCLK, negedge ADDRH[2], 0:0:0, 0:0:0, notifier,sh_we_clk_en_p,sh_we_clk_en_p,WCLK_dly,ADDRH_dly[2]);
  $setuphold (posedge WCLK, negedge ADDRH[3], 0:0:0, 0:0:0, notifier,sh_we_clk_en_p,sh_we_clk_en_p,WCLK_dly,ADDRH_dly[3]);
  $setuphold (posedge WCLK, negedge ADDRH[4], 0:0:0, 0:0:0, notifier,sh_we_clk_en_p,sh_we_clk_en_p,WCLK_dly,ADDRH_dly[4]);
  $setuphold (posedge WCLK, negedge DIA[0], 0:0:0, 0:0:0, notifier,sh_we_clk_en_p,sh_we_clk_en_p,WCLK_dly,DIA_dly[0]);
  $setuphold (posedge WCLK, negedge DIA[1], 0:0:0, 0:0:0, notifier,sh_we_clk_en_p,sh_we_clk_en_p,WCLK_dly,DIA_dly[1]);
  $setuphold (posedge WCLK, negedge DIB[0], 0:0:0, 0:0:0, notifier,sh_we_clk_en_p,sh_we_clk_en_p,WCLK_dly,DIB_dly[0]);
  $setuphold (posedge WCLK, negedge DIB[1], 0:0:0, 0:0:0, notifier,sh_we_clk_en_p,sh_we_clk_en_p,WCLK_dly,DIB_dly[1]);
  $setuphold (posedge WCLK, negedge DIC[0], 0:0:0, 0:0:0, notifier,sh_we_clk_en_p,sh_we_clk_en_p,WCLK_dly,DIC_dly[0]);
  $setuphold (posedge WCLK, negedge DIC[1], 0:0:0, 0:0:0, notifier,sh_we_clk_en_p,sh_we_clk_en_p,WCLK_dly,DIC_dly[1]);
  $setuphold (posedge WCLK, negedge DID[0], 0:0:0, 0:0:0, notifier,sh_we_clk_en_p,sh_we_clk_en_p,WCLK_dly,DID_dly[0]);
  $setuphold (posedge WCLK, negedge DID[1], 0:0:0, 0:0:0, notifier,sh_we_clk_en_p,sh_we_clk_en_p,WCLK_dly,DID_dly[1]);
  $setuphold (posedge WCLK, negedge DIE[0], 0:0:0, 0:0:0, notifier,sh_we_clk_en_p,sh_we_clk_en_p,WCLK_dly,DIE_dly[0]);
  $setuphold (posedge WCLK, negedge DIE[1], 0:0:0, 0:0:0, notifier,sh_we_clk_en_p,sh_we_clk_en_p,WCLK_dly,DIE_dly[1]);
  $setuphold (posedge WCLK, negedge DIF[0], 0:0:0, 0:0:0, notifier,sh_we_clk_en_p,sh_we_clk_en_p,WCLK_dly,DIF_dly[0]);
  $setuphold (posedge WCLK, negedge DIF[1], 0:0:0, 0:0:0, notifier,sh_we_clk_en_p,sh_we_clk_en_p,WCLK_dly,DIF_dly[1]);
  $setuphold (posedge WCLK, negedge DIG[0], 0:0:0, 0:0:0, notifier,sh_we_clk_en_p,sh_we_clk_en_p,WCLK_dly,DIG_dly[0]);
  $setuphold (posedge WCLK, negedge DIG[1], 0:0:0, 0:0:0, notifier,sh_we_clk_en_p,sh_we_clk_en_p,WCLK_dly,DIG_dly[1]);
  $setuphold (posedge WCLK, negedge DIH[0], 0:0:0, 0:0:0, notifier,sh_we_clk_en_p,sh_we_clk_en_p,WCLK_dly,DIH_dly[0]);
  $setuphold (posedge WCLK, negedge DIH[1], 0:0:0, 0:0:0, notifier,sh_we_clk_en_p,sh_we_clk_en_p,WCLK_dly,DIH_dly[1]);
  $setuphold (posedge WCLK, negedge WE, 0:0:0, 0:0:0, notifier,sh_clk_en_p,sh_clk_en_p,WCLK_dly,WE_dly);
  $setuphold (posedge WCLK, posedge ADDRH[0], 0:0:0, 0:0:0, notifier,sh_we_clk_en_p,sh_we_clk_en_p,WCLK_dly,ADDRH_dly[0]);
  $setuphold (posedge WCLK, posedge ADDRH[1], 0:0:0, 0:0:0, notifier,sh_we_clk_en_p,sh_we_clk_en_p,WCLK_dly,ADDRH_dly[1]);
  $setuphold (posedge WCLK, posedge ADDRH[2], 0:0:0, 0:0:0, notifier,sh_we_clk_en_p,sh_we_clk_en_p,WCLK_dly,ADDRH_dly[2]);
  $setuphold (posedge WCLK, posedge ADDRH[3], 0:0:0, 0:0:0, notifier,sh_we_clk_en_p,sh_we_clk_en_p,WCLK_dly,ADDRH_dly[3]);
  $setuphold (posedge WCLK, posedge ADDRH[4], 0:0:0, 0:0:0, notifier,sh_we_clk_en_p,sh_we_clk_en_p,WCLK_dly,ADDRH_dly[4]);
  $setuphold (posedge WCLK, posedge DIA[0], 0:0:0, 0:0:0, notifier,sh_we_clk_en_p,sh_we_clk_en_p,WCLK_dly,DIA_dly[0]);
  $setuphold (posedge WCLK, posedge DIA[1], 0:0:0, 0:0:0, notifier,sh_we_clk_en_p,sh_we_clk_en_p,WCLK_dly,DIA_dly[1]);
  $setuphold (posedge WCLK, posedge DIB[0], 0:0:0, 0:0:0, notifier,sh_we_clk_en_p,sh_we_clk_en_p,WCLK_dly,DIB_dly[0]);
  $setuphold (posedge WCLK, posedge DIB[1], 0:0:0, 0:0:0, notifier,sh_we_clk_en_p,sh_we_clk_en_p,WCLK_dly,DIB_dly[1]);
  $setuphold (posedge WCLK, posedge DIC[0], 0:0:0, 0:0:0, notifier,sh_we_clk_en_p,sh_we_clk_en_p,WCLK_dly,DIC_dly[0]);
  $setuphold (posedge WCLK, posedge DIC[1], 0:0:0, 0:0:0, notifier,sh_we_clk_en_p,sh_we_clk_en_p,WCLK_dly,DIC_dly[1]);
  $setuphold (posedge WCLK, posedge DID[0], 0:0:0, 0:0:0, notifier,sh_we_clk_en_p,sh_we_clk_en_p,WCLK_dly,DID_dly[0]);
  $setuphold (posedge WCLK, posedge DID[1], 0:0:0, 0:0:0, notifier,sh_we_clk_en_p,sh_we_clk_en_p,WCLK_dly,DID_dly[1]);
  $setuphold (posedge WCLK, posedge DIE[0], 0:0:0, 0:0:0, notifier,sh_we_clk_en_p,sh_we_clk_en_p,WCLK_dly,DIE_dly[0]);
  $setuphold (posedge WCLK, posedge DIE[1], 0:0:0, 0:0:0, notifier,sh_we_clk_en_p,sh_we_clk_en_p,WCLK_dly,DIE_dly[1]);
  $setuphold (posedge WCLK, posedge DIF[0], 0:0:0, 0:0:0, notifier,sh_we_clk_en_p,sh_we_clk_en_p,WCLK_dly,DIF_dly[0]);
  $setuphold (posedge WCLK, posedge DIF[1], 0:0:0, 0:0:0, notifier,sh_we_clk_en_p,sh_we_clk_en_p,WCLK_dly,DIF_dly[1]);
  $setuphold (posedge WCLK, posedge DIG[0], 0:0:0, 0:0:0, notifier,sh_we_clk_en_p,sh_we_clk_en_p,WCLK_dly,DIG_dly[0]);
  $setuphold (posedge WCLK, posedge DIG[1], 0:0:0, 0:0:0, notifier,sh_we_clk_en_p,sh_we_clk_en_p,WCLK_dly,DIG_dly[1]);
  $setuphold (posedge WCLK, posedge DIH[0], 0:0:0, 0:0:0, notifier,sh_we_clk_en_p,sh_we_clk_en_p,WCLK_dly,DIH_dly[0]);
  $setuphold (posedge WCLK, posedge DIH[1], 0:0:0, 0:0:0, notifier,sh_we_clk_en_p,sh_we_clk_en_p,WCLK_dly,DIH_dly[1]);
  $setuphold (posedge WCLK, posedge WE, 0:0:0, 0:0:0, notifier,sh_clk_en_p,sh_clk_en_p,WCLK_dly,WE_dly);
   specparam PATHPULSE$ = 0;
  endspecify
`endif

endmodule

`endcelldefine
