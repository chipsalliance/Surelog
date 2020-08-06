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

`ifdef XIL_ATTR_TEST
  reg attr_test = 1'b1;
`else
  reg attr_test = 1'b0;
`endif
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

`ifdef XIL_TIMING
  wire [5:0] ADDRH_dly;
  wire DIA_dly;
  wire DIB_dly;
  wire DIC_dly;
  wire DID_dly;
  wire DIE_dly;
  wire DIF_dly;
  wire DIG_dly;
  wire DIH_dly;
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

`ifdef XIL_TIMING
  always @(notifier) begin
      mem_a[ADDRH_in] <= 1'bx;
      mem_b[ADDRH_in] <= 1'bx;
      mem_c[ADDRH_in] <= 1'bx;
      mem_d[ADDRH_in] <= 1'bx;
      mem_e[ADDRH_in] <= 1'bx;
      mem_f[ADDRH_in] <= 1'bx;
      mem_g[ADDRH_in] <= 1'bx;
      mem_h[ADDRH_in] <= 1'bx;
  end

  assign sh_clk_en_p = ~IS_WCLK_INVERTED_BIN;
  assign sh_clk_en_n = IS_WCLK_INVERTED_BIN;
  assign sh_we_clk_en_p = WE_in && ~IS_WCLK_INVERTED_BIN;
  assign sh_we_clk_en_n = WE_in && IS_WCLK_INVERTED_BIN;

  specify
   (WCLK => DOA) = (0:0:0, 0:0:0);
   (WCLK => DOB) = (0:0:0, 0:0:0);
   (WCLK => DOC) = (0:0:0, 0:0:0);
   (WCLK => DOD) = (0:0:0, 0:0:0);
   (WCLK => DOE) = (0:0:0, 0:0:0);
   (WCLK => DOF) = (0:0:0, 0:0:0);
   (WCLK => DOG) = (0:0:0, 0:0:0);
   (WCLK => DOH) = (0:0:0, 0:0:0);
   (ADDRA *> DOA) = (0:0:0, 0:0:0);
   (ADDRB *> DOB) = (0:0:0, 0:0:0);
   (ADDRC *> DOC) = (0:0:0, 0:0:0);
   (ADDRD *> DOD) = (0:0:0, 0:0:0);
   (ADDRE *> DOE) = (0:0:0, 0:0:0);
   (ADDRF *> DOF) = (0:0:0, 0:0:0);
   (ADDRG *> DOG) = (0:0:0, 0:0:0);
   (ADDRH *> DOH) = (0:0:0, 0:0:0);
   $period (negedge WCLK &&& WE, 0:0:0, notifier);
   $period (posedge WCLK &&& WE, 0:0:0, notifier);
   $setuphold (negedge WCLK, negedge ADDRH[0], 0:0:0, 0:0:0, notifier,sh_we_clk_en_n,sh_we_clk_en_n,WCLK_dly,ADDRH_dly[0]);
   $setuphold (negedge WCLK, negedge ADDRH[1], 0:0:0, 0:0:0, notifier,sh_we_clk_en_n,sh_we_clk_en_n,WCLK_dly,ADDRH_dly[1]);
   $setuphold (negedge WCLK, negedge ADDRH[2], 0:0:0, 0:0:0, notifier,sh_we_clk_en_n,sh_we_clk_en_n,WCLK_dly,ADDRH_dly[2]);
   $setuphold (negedge WCLK, negedge ADDRH[3], 0:0:0, 0:0:0, notifier,sh_we_clk_en_n,sh_we_clk_en_n,WCLK_dly,ADDRH_dly[3]);
   $setuphold (negedge WCLK, negedge ADDRH[4], 0:0:0, 0:0:0, notifier,sh_we_clk_en_n,sh_we_clk_en_n,WCLK_dly,ADDRH_dly[4]);
   $setuphold (negedge WCLK, negedge ADDRH[5], 0:0:0, 0:0:0, notifier,sh_we_clk_en_n,sh_we_clk_en_n,WCLK_dly,ADDRH_dly[5]);
   $setuphold (negedge WCLK, negedge DIA, 0:0:0, 0:0:0, notifier,sh_we_clk_en_n,sh_we_clk_en_n,WCLK_dly,DIA_dly);
   $setuphold (negedge WCLK, negedge DIB, 0:0:0, 0:0:0, notifier,sh_we_clk_en_n,sh_we_clk_en_n,WCLK_dly,DIB_dly);
   $setuphold (negedge WCLK, negedge DIC, 0:0:0, 0:0:0, notifier,sh_we_clk_en_n,sh_we_clk_en_n,WCLK_dly,DIC_dly);
   $setuphold (negedge WCLK, negedge DID, 0:0:0, 0:0:0, notifier,sh_we_clk_en_n,sh_we_clk_en_n,WCLK_dly,DID_dly);
   $setuphold (negedge WCLK, negedge DIE, 0:0:0, 0:0:0, notifier,sh_we_clk_en_n,sh_we_clk_en_n,WCLK_dly,DIE_dly);
   $setuphold (negedge WCLK, negedge DIF, 0:0:0, 0:0:0, notifier,sh_we_clk_en_n,sh_we_clk_en_n,WCLK_dly,DIF_dly);
   $setuphold (negedge WCLK, negedge DIG, 0:0:0, 0:0:0, notifier,sh_we_clk_en_n,sh_we_clk_en_n,WCLK_dly,DIG_dly);
   $setuphold (negedge WCLK, negedge DIH, 0:0:0, 0:0:0, notifier,sh_we_clk_en_n,sh_we_clk_en_n,WCLK_dly,DIH_dly);
   $setuphold (negedge WCLK, negedge WE, 0:0:0, 0:0:0, notifier,sh_clk_en_n,sh_clk_en_n,WCLK_dly,WE_dly);
   $setuphold (negedge WCLK, posedge ADDRH[0], 0:0:0, 0:0:0, notifier,sh_we_clk_en_n,sh_we_clk_en_n,WCLK_dly,ADDRH_dly[0]);
   $setuphold (negedge WCLK, posedge ADDRH[1], 0:0:0, 0:0:0, notifier,sh_we_clk_en_n,sh_we_clk_en_n,WCLK_dly,ADDRH_dly[1]);
   $setuphold (negedge WCLK, posedge ADDRH[2], 0:0:0, 0:0:0, notifier,sh_we_clk_en_n,sh_we_clk_en_n,WCLK_dly,ADDRH_dly[2]);
   $setuphold (negedge WCLK, posedge ADDRH[3], 0:0:0, 0:0:0, notifier,sh_we_clk_en_n,sh_we_clk_en_n,WCLK_dly,ADDRH_dly[3]);
   $setuphold (negedge WCLK, posedge ADDRH[4], 0:0:0, 0:0:0, notifier,sh_we_clk_en_n,sh_we_clk_en_n,WCLK_dly,ADDRH_dly[4]);
   $setuphold (negedge WCLK, posedge ADDRH[5], 0:0:0, 0:0:0, notifier,sh_we_clk_en_n,sh_we_clk_en_n,WCLK_dly,ADDRH_dly[5]);
   $setuphold (negedge WCLK, posedge DIA, 0:0:0, 0:0:0, notifier,sh_we_clk_en_n,sh_we_clk_en_n,WCLK_dly,DIA_dly);
   $setuphold (negedge WCLK, posedge DIB, 0:0:0, 0:0:0, notifier,sh_we_clk_en_n,sh_we_clk_en_n,WCLK_dly,DIB_dly);
   $setuphold (negedge WCLK, posedge DIC, 0:0:0, 0:0:0, notifier,sh_we_clk_en_n,sh_we_clk_en_n,WCLK_dly,DIC_dly);
   $setuphold (negedge WCLK, posedge DID, 0:0:0, 0:0:0, notifier,sh_we_clk_en_n,sh_we_clk_en_n,WCLK_dly,DID_dly);
   $setuphold (negedge WCLK, posedge DIE, 0:0:0, 0:0:0, notifier,sh_we_clk_en_n,sh_we_clk_en_n,WCLK_dly,DIE_dly);
   $setuphold (negedge WCLK, posedge DIF, 0:0:0, 0:0:0, notifier,sh_we_clk_en_n,sh_we_clk_en_n,WCLK_dly,DIF_dly);
   $setuphold (negedge WCLK, posedge DIG, 0:0:0, 0:0:0, notifier,sh_we_clk_en_n,sh_we_clk_en_n,WCLK_dly,DIG_dly);
   $setuphold (negedge WCLK, posedge DIH, 0:0:0, 0:0:0, notifier,sh_we_clk_en_n,sh_we_clk_en_n,WCLK_dly,DIH_dly);
   $setuphold (negedge WCLK, posedge WE, 0:0:0, 0:0:0, notifier,sh_clk_en_n,sh_clk_en_n,WCLK_dly,WE_dly);
   $setuphold (posedge WCLK, negedge ADDRH[0], 0:0:0, 0:0:0, notifier,sh_we_clk_en_p,sh_we_clk_en_p,WCLK_dly,ADDRH_dly[0]);
   $setuphold (posedge WCLK, negedge ADDRH[1], 0:0:0, 0:0:0, notifier,sh_we_clk_en_p,sh_we_clk_en_p,WCLK_dly,ADDRH_dly[1]);
   $setuphold (posedge WCLK, negedge ADDRH[2], 0:0:0, 0:0:0, notifier,sh_we_clk_en_p,sh_we_clk_en_p,WCLK_dly,ADDRH_dly[2]);
   $setuphold (posedge WCLK, negedge ADDRH[3], 0:0:0, 0:0:0, notifier,sh_we_clk_en_p,sh_we_clk_en_p,WCLK_dly,ADDRH_dly[3]);
   $setuphold (posedge WCLK, negedge ADDRH[4], 0:0:0, 0:0:0, notifier,sh_we_clk_en_p,sh_we_clk_en_p,WCLK_dly,ADDRH_dly[4]);
   $setuphold (posedge WCLK, negedge ADDRH[5], 0:0:0, 0:0:0, notifier,sh_we_clk_en_p,sh_we_clk_en_p,WCLK_dly,ADDRH_dly[5]);
   $setuphold (posedge WCLK, negedge DIA, 0:0:0, 0:0:0, notifier,sh_we_clk_en_p,sh_we_clk_en_p,WCLK_dly,DIA_dly);
   $setuphold (posedge WCLK, negedge DIB, 0:0:0, 0:0:0, notifier,sh_we_clk_en_p,sh_we_clk_en_p,WCLK_dly,DIB_dly);
   $setuphold (posedge WCLK, negedge DIC, 0:0:0, 0:0:0, notifier,sh_we_clk_en_p,sh_we_clk_en_p,WCLK_dly,DIC_dly);
   $setuphold (posedge WCLK, negedge DID, 0:0:0, 0:0:0, notifier,sh_we_clk_en_p,sh_we_clk_en_p,WCLK_dly,DID_dly);
   $setuphold (posedge WCLK, negedge DIE, 0:0:0, 0:0:0, notifier,sh_we_clk_en_p,sh_we_clk_en_p,WCLK_dly,DIE_dly);
   $setuphold (posedge WCLK, negedge DIF, 0:0:0, 0:0:0, notifier,sh_we_clk_en_p,sh_we_clk_en_p,WCLK_dly,DIF_dly);
   $setuphold (posedge WCLK, negedge DIG, 0:0:0, 0:0:0, notifier,sh_we_clk_en_p,sh_we_clk_en_p,WCLK_dly,DIG_dly);
   $setuphold (posedge WCLK, negedge DIH, 0:0:0, 0:0:0, notifier,sh_we_clk_en_p,sh_we_clk_en_p,WCLK_dly,DIH_dly);
   $setuphold (posedge WCLK, negedge WE, 0:0:0, 0:0:0, notifier,sh_clk_en_p,sh_clk_en_p,WCLK_dly,WE_dly);
   $setuphold (posedge WCLK, posedge ADDRH[0], 0:0:0, 0:0:0, notifier,sh_we_clk_en_p,sh_we_clk_en_p,WCLK_dly,ADDRH_dly[0]);
   $setuphold (posedge WCLK, posedge ADDRH[1], 0:0:0, 0:0:0, notifier,sh_we_clk_en_p,sh_we_clk_en_p,WCLK_dly,ADDRH_dly[1]);
   $setuphold (posedge WCLK, posedge ADDRH[2], 0:0:0, 0:0:0, notifier,sh_we_clk_en_p,sh_we_clk_en_p,WCLK_dly,ADDRH_dly[2]);
   $setuphold (posedge WCLK, posedge ADDRH[3], 0:0:0, 0:0:0, notifier,sh_we_clk_en_p,sh_we_clk_en_p,WCLK_dly,ADDRH_dly[3]);
   $setuphold (posedge WCLK, posedge ADDRH[4], 0:0:0, 0:0:0, notifier,sh_we_clk_en_p,sh_we_clk_en_p,WCLK_dly,ADDRH_dly[4]);
   $setuphold (posedge WCLK, posedge ADDRH[5], 0:0:0, 0:0:0, notifier,sh_we_clk_en_p,sh_we_clk_en_p,WCLK_dly,ADDRH_dly[5]);
   $setuphold (posedge WCLK, posedge DIA, 0:0:0, 0:0:0, notifier,sh_we_clk_en_p,sh_we_clk_en_p,WCLK_dly,DIA_dly);
   $setuphold (posedge WCLK, posedge DIB, 0:0:0, 0:0:0, notifier,sh_we_clk_en_p,sh_we_clk_en_p,WCLK_dly,DIB_dly);
   $setuphold (posedge WCLK, posedge DIC, 0:0:0, 0:0:0, notifier,sh_we_clk_en_p,sh_we_clk_en_p,WCLK_dly,DIC_dly);
   $setuphold (posedge WCLK, posedge DID, 0:0:0, 0:0:0, notifier,sh_we_clk_en_p,sh_we_clk_en_p,WCLK_dly,DID_dly);
   $setuphold (posedge WCLK, posedge DIE, 0:0:0, 0:0:0, notifier,sh_we_clk_en_p,sh_we_clk_en_p,WCLK_dly,DIE_dly);
   $setuphold (posedge WCLK, posedge DIF, 0:0:0, 0:0:0, notifier,sh_we_clk_en_p,sh_we_clk_en_p,WCLK_dly,DIF_dly);
   $setuphold (posedge WCLK, posedge DIG, 0:0:0, 0:0:0, notifier,sh_we_clk_en_p,sh_we_clk_en_p,WCLK_dly,DIG_dly);
   $setuphold (posedge WCLK, posedge DIH, 0:0:0, 0:0:0, notifier,sh_we_clk_en_p,sh_we_clk_en_p,WCLK_dly,DIH_dly);
   $setuphold (posedge WCLK, posedge WE, 0:0:0, 0:0:0, notifier,sh_clk_en_p,sh_clk_en_p,WCLK_dly,WE_dly);
   specparam PATHPULSE$ = 0;
  endspecify
`endif

endmodule

`endcelldefine
