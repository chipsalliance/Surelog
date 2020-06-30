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
//  /   /                        64-Deep by 4-bit Wide Multi Port RAM
// /___/   /\      Filename    : RAM64M.v
// \   \  /  \
//  \___\/\___\
//
///////////////////////////////////////////////////////////////////////////////
// Revision:
//    03/21/06 - Initial version.
//    12/01/06 - Fix the cut/past error for port C and D (CR 430051)
//    05/07/08 - Add negative setup/hold support (CR468872)
//    12/13/11 - Added `celldefine and `endcelldefine (CR 524859).
//    04/18/13 - PR683925 - add invertible pin support.
//    10/22/14 - Added #1 to $finish (CR 808642).
// End Revision:
///////////////////////////////////////////////////////////////////////////////

`timescale 1 ps / 1 ps

`celldefine

module RAM64M #(
`ifdef XIL_TIMING
  parameter LOC = "UNPLACED",
`endif
  parameter [63:0] INIT_A = 64'h0000000000000000,
  parameter [63:0] INIT_B = 64'h0000000000000000,
  parameter [63:0] INIT_C = 64'h0000000000000000,
  parameter [63:0] INIT_D = 64'h0000000000000000,
  parameter [0:0] IS_WCLK_INVERTED = 1'b0
)(
  output DOA,
  output DOB,
  output DOC,
  output DOD,

  input [5:0] ADDRA,
  input [5:0] ADDRB,
  input [5:0] ADDRC,
  input [5:0] ADDRD,
  input DIA,
  input DIB,
  input DIC,
  input DID,
  input WCLK,
  input WE
);
  
// define constants
  localparam MODULE_NAME = "RAM64M";

  reg trig_attr = 1'b0;

`ifdef XIL_ATTR_TEST
  reg attr_test = 1'b1;
`else
  reg attr_test = 1'b0;
`endif
  reg attr_err = 1'b0;

  wire IS_WCLK_INVERTED_BIN;

  wire [5:0] ADDRD_in;
  wire DIA_in;
  wire DIB_in;
  wire DIC_in;
  wire DID_in;
  wire WCLK_in;
  wire WE_in;

`ifdef XIL_TIMING
  wire [5:0] ADDRD_dly;
  wire DIA_dly;
  wire DIB_dly;
  wire DIC_dly;
  wire DID_dly;
  wire WCLK_dly;
  wire WE_dly;

  reg notifier;

  wire sh_clk_en_p;
  wire sh_clk_en_n;
  wire sh_we_clk_en_p;
  wire sh_we_clk_en_n;

  assign ADDRD_in = ADDRD_dly;
  assign DIA_in = DIA_dly;
  assign DIB_in = DIB_dly;
  assign DIC_in = DIC_dly;
  assign DID_in = DID_dly;
  assign WCLK_in = WCLK_dly ^ IS_WCLK_INVERTED_BIN;
  assign WE_in = (WE === 1'bz) || WE_dly; // rv 1
`else
  assign ADDRD_in = ADDRD;
  assign DIA_in = DIA;
  assign DIB_in = DIB;
  assign DIC_in = DIC;
  assign DID_in = DID;
  assign WCLK_in = WCLK ^ IS_WCLK_INVERTED_BIN;
  assign WE_in = (WE === 1'bz) || WE; // rv 1
`endif

  assign IS_WCLK_INVERTED_BIN = IS_WCLK_INVERTED;

  reg [63:0] mem_a, mem_b, mem_c, mem_d;

  initial begin
    mem_a = INIT_A;
    mem_b = INIT_B;
    mem_c = INIT_C;
    mem_d = INIT_D;
  end

  always @(posedge WCLK_in)
    if (WE_in) begin
      mem_a[ADDRD_in] <= #100 DIA_in;
      mem_b[ADDRD_in] <= #100 DIB_in;
      mem_c[ADDRD_in] <= #100 DIC_in;
      mem_d[ADDRD_in] <= #100 DID_in;
  end

   assign  DOA = mem_a[ADDRA];
   assign  DOB = mem_b[ADDRB];
   assign  DOC = mem_c[ADDRC];
   assign  DOD = mem_d[ADDRD_in];

`ifdef XIL_TIMING
  always @(notifier) begin
      mem_a[ADDRD_in] <= 1'bx;
      mem_b[ADDRD_in] <= 1'bx;
      mem_c[ADDRD_in] <= 1'bx;
      mem_d[ADDRD_in] <= 1'bx;
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
   (ADDRA *> DOA) = (0:0:0, 0:0:0);
   (ADDRB *> DOB) = (0:0:0, 0:0:0);
   (ADDRC *> DOC) = (0:0:0, 0:0:0);
   (ADDRD *> DOD) = (0:0:0, 0:0:0);
   $period (negedge WCLK &&& WE, 0:0:0, notifier);
   $period (posedge WCLK &&& WE, 0:0:0, notifier);
   $setuphold (negedge WCLK, negedge ADDRD[0], 0:0:0, 0:0:0, notifier,sh_we_clk_en_n,sh_we_clk_en_n,WCLK_dly,ADDRD_dly[0]);
   $setuphold (negedge WCLK, negedge ADDRD[1], 0:0:0, 0:0:0, notifier,sh_we_clk_en_n,sh_we_clk_en_n,WCLK_dly,ADDRD_dly[1]);
   $setuphold (negedge WCLK, negedge ADDRD[2], 0:0:0, 0:0:0, notifier,sh_we_clk_en_n,sh_we_clk_en_n,WCLK_dly,ADDRD_dly[2]);
   $setuphold (negedge WCLK, negedge ADDRD[3], 0:0:0, 0:0:0, notifier,sh_we_clk_en_n,sh_we_clk_en_n,WCLK_dly,ADDRD_dly[3]);
   $setuphold (negedge WCLK, negedge ADDRD[4], 0:0:0, 0:0:0, notifier,sh_we_clk_en_n,sh_we_clk_en_n,WCLK_dly,ADDRD_dly[4]);
   $setuphold (negedge WCLK, negedge ADDRD[5], 0:0:0, 0:0:0, notifier,sh_we_clk_en_n,sh_we_clk_en_n,WCLK_dly,ADDRD_dly[5]);
   $setuphold (negedge WCLK, negedge DIA, 0:0:0, 0:0:0, notifier,sh_we_clk_en_n,sh_we_clk_en_n,WCLK_dly,DIA_dly);
   $setuphold (negedge WCLK, negedge DIB, 0:0:0, 0:0:0, notifier,sh_we_clk_en_n,sh_we_clk_en_n,WCLK_dly,DIB_dly);
   $setuphold (negedge WCLK, negedge DIC, 0:0:0, 0:0:0, notifier,sh_we_clk_en_n,sh_we_clk_en_n,WCLK_dly,DIC_dly);
   $setuphold (negedge WCLK, negedge DID, 0:0:0, 0:0:0, notifier,sh_we_clk_en_n,sh_we_clk_en_n,WCLK_dly,DID_dly);
   $setuphold (negedge WCLK, negedge WE, 0:0:0, 0:0:0, notifier,sh_clk_en_n,sh_clk_en_n,WCLK_dly,WE_dly);
   $setuphold (negedge WCLK, posedge ADDRD[0], 0:0:0, 0:0:0, notifier,sh_we_clk_en_n,sh_we_clk_en_n,WCLK_dly,ADDRD_dly[0]);
   $setuphold (negedge WCLK, posedge ADDRD[1], 0:0:0, 0:0:0, notifier,sh_we_clk_en_n,sh_we_clk_en_n,WCLK_dly,ADDRD_dly[1]);
   $setuphold (negedge WCLK, posedge ADDRD[2], 0:0:0, 0:0:0, notifier,sh_we_clk_en_n,sh_we_clk_en_n,WCLK_dly,ADDRD_dly[2]);
   $setuphold (negedge WCLK, posedge ADDRD[3], 0:0:0, 0:0:0, notifier,sh_we_clk_en_n,sh_we_clk_en_n,WCLK_dly,ADDRD_dly[3]);
   $setuphold (negedge WCLK, posedge ADDRD[4], 0:0:0, 0:0:0, notifier,sh_we_clk_en_n,sh_we_clk_en_n,WCLK_dly,ADDRD_dly[4]);
   $setuphold (negedge WCLK, posedge ADDRD[5], 0:0:0, 0:0:0, notifier,sh_we_clk_en_n,sh_we_clk_en_n,WCLK_dly,ADDRD_dly[5]);
   $setuphold (negedge WCLK, posedge DIA, 0:0:0, 0:0:0, notifier,sh_we_clk_en_n,sh_we_clk_en_n,WCLK_dly,DIA_dly);
   $setuphold (negedge WCLK, posedge DIB, 0:0:0, 0:0:0, notifier,sh_we_clk_en_n,sh_we_clk_en_n,WCLK_dly,DIB_dly);
   $setuphold (negedge WCLK, posedge DIC, 0:0:0, 0:0:0, notifier,sh_we_clk_en_n,sh_we_clk_en_n,WCLK_dly,DIC_dly);
   $setuphold (negedge WCLK, posedge DID, 0:0:0, 0:0:0, notifier,sh_we_clk_en_n,sh_we_clk_en_n,WCLK_dly,DID_dly);
   $setuphold (negedge WCLK, posedge WE, 0:0:0, 0:0:0, notifier,sh_clk_en_n,sh_clk_en_n,WCLK_dly,WE_dly);
   $setuphold (posedge WCLK, negedge ADDRD[0], 0:0:0, 0:0:0, notifier,sh_we_clk_en_p,sh_we_clk_en_p,WCLK_dly,ADDRD_dly[0]);
   $setuphold (posedge WCLK, negedge ADDRD[1], 0:0:0, 0:0:0, notifier,sh_we_clk_en_p,sh_we_clk_en_p,WCLK_dly,ADDRD_dly[1]);
   $setuphold (posedge WCLK, negedge ADDRD[2], 0:0:0, 0:0:0, notifier,sh_we_clk_en_p,sh_we_clk_en_p,WCLK_dly,ADDRD_dly[2]);
   $setuphold (posedge WCLK, negedge ADDRD[3], 0:0:0, 0:0:0, notifier,sh_we_clk_en_p,sh_we_clk_en_p,WCLK_dly,ADDRD_dly[3]);
   $setuphold (posedge WCLK, negedge ADDRD[4], 0:0:0, 0:0:0, notifier,sh_we_clk_en_p,sh_we_clk_en_p,WCLK_dly,ADDRD_dly[4]);
   $setuphold (posedge WCLK, negedge ADDRD[5], 0:0:0, 0:0:0, notifier,sh_we_clk_en_p,sh_we_clk_en_p,WCLK_dly,ADDRD_dly[5]);
   $setuphold (posedge WCLK, negedge DIA, 0:0:0, 0:0:0, notifier,sh_we_clk_en_p,sh_we_clk_en_p,WCLK_dly,DIA_dly);
   $setuphold (posedge WCLK, negedge DIB, 0:0:0, 0:0:0, notifier,sh_we_clk_en_p,sh_we_clk_en_p,WCLK_dly,DIB_dly);
   $setuphold (posedge WCLK, negedge DIC, 0:0:0, 0:0:0, notifier,sh_we_clk_en_p,sh_we_clk_en_p,WCLK_dly,DIC_dly);
   $setuphold (posedge WCLK, negedge DID, 0:0:0, 0:0:0, notifier,sh_we_clk_en_p,sh_we_clk_en_p,WCLK_dly,DID_dly);
   $setuphold (posedge WCLK, negedge WE, 0:0:0, 0:0:0, notifier,sh_clk_en_p,sh_clk_en_p,WCLK_dly,WE_dly);
   $setuphold (posedge WCLK, posedge ADDRD[0], 0:0:0, 0:0:0, notifier,sh_we_clk_en_p,sh_we_clk_en_p,WCLK_dly,ADDRD_dly[0]);
   $setuphold (posedge WCLK, posedge ADDRD[1], 0:0:0, 0:0:0, notifier,sh_we_clk_en_p,sh_we_clk_en_p,WCLK_dly,ADDRD_dly[1]);
   $setuphold (posedge WCLK, posedge ADDRD[2], 0:0:0, 0:0:0, notifier,sh_we_clk_en_p,sh_we_clk_en_p,WCLK_dly,ADDRD_dly[2]);
   $setuphold (posedge WCLK, posedge ADDRD[3], 0:0:0, 0:0:0, notifier,sh_we_clk_en_p,sh_we_clk_en_p,WCLK_dly,ADDRD_dly[3]);
   $setuphold (posedge WCLK, posedge ADDRD[4], 0:0:0, 0:0:0, notifier,sh_we_clk_en_p,sh_we_clk_en_p,WCLK_dly,ADDRD_dly[4]);
   $setuphold (posedge WCLK, posedge ADDRD[5], 0:0:0, 0:0:0, notifier,sh_we_clk_en_p,sh_we_clk_en_p,WCLK_dly,ADDRD_dly[5]);
   $setuphold (posedge WCLK, posedge DIA, 0:0:0, 0:0:0, notifier,sh_we_clk_en_p,sh_we_clk_en_p,WCLK_dly,DIA_dly);
   $setuphold (posedge WCLK, posedge DIB, 0:0:0, 0:0:0, notifier,sh_we_clk_en_p,sh_we_clk_en_p,WCLK_dly,DIB_dly);
   $setuphold (posedge WCLK, posedge DIC, 0:0:0, 0:0:0, notifier,sh_we_clk_en_p,sh_we_clk_en_p,WCLK_dly,DIC_dly);
   $setuphold (posedge WCLK, posedge DID, 0:0:0, 0:0:0, notifier,sh_we_clk_en_p,sh_we_clk_en_p,WCLK_dly,DID_dly);
   $setuphold (posedge WCLK, posedge WE, 0:0:0, 0:0:0, notifier,sh_clk_en_p,sh_clk_en_p,WCLK_dly,WE_dly);
   specparam PATHPULSE$ = 0;
  endspecify
`endif

endmodule

`endcelldefine
