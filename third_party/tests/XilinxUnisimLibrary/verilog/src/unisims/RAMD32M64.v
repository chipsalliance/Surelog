///////////////////////////////////////////////////////////////////////////////
//     Copyright (c) 1995/2019 Xilinx, Inc.
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
// \   \   \/      Version     : 2019.2
//  \   \          Description : Xilinx Unified Simulation Library Component
//  /   /                        RAMD32M64
// /___/   /\      Filename    : RAMD32M64.v
// \   \  /  \
//  \___\/\___\
//
///////////////////////////////////////////////////////////////////////////////
//  Revision:
//
//  End Revision:
///////////////////////////////////////////////////////////////////////////////

`timescale 1 ps / 1 ps

`celldefine

module RAMD32M64 #(
`ifdef XIL_TIMING
  parameter LOC = "UNPLACED",
`endif
  parameter [63:0] INIT = 64'h0000000000000000,
  parameter [0:0] IS_CLK_INVERTED = 1'b0
)(
  output O,

  input CLK,
  input I,
  input RADR0,
  input RADR1,
  input RADR2,
  input RADR3,
  input RADR4,
  input RADR5,
  input WADR0,
  input WADR1,
  input WADR2,
  input WADR3,
  input WADR4,
  input WE
);

// define constants
  localparam MODULE_NAME = "RAMD32M64";
  
  reg trig_attr;
// include dynamic registers - XILINX test only
`ifdef XIL_DR
  `include "RAMD32M64_dr.v"
`else
  reg [63:0] INIT_REG = INIT;
  reg [0:0] IS_CLK_INVERTED_REG = IS_CLK_INVERTED;
`endif

`ifdef XIL_XECLIB
reg glblGSR = 1'b0;
`else
tri0 glblGSR = glbl.GSR;
`endif

  wire CLK_in;
  wire I_in;
  wire RADR0_in;
  wire RADR1_in;
  wire RADR2_in;
  wire RADR3_in;
  wire RADR4_in;
  wire RADR5_in;
  wire WADR0_in;
  wire WADR1_in;
  wire WADR2_in;
  wire WADR3_in;
  wire WADR4_in;
  wire WE_in;

`ifdef XIL_TIMING
  wire CLK_delay;
  wire I_delay;
  wire RADR0_delay;
  wire RADR1_delay;
  wire RADR2_delay;
  wire RADR3_delay;
  wire RADR4_delay;
  wire RADR5_delay;
  wire WADR0_delay;
  wire WADR1_delay;
  wire WADR2_delay;
  wire WADR3_delay;
  wire WADR4_delay;
  wire WE_delay;
`endif

`ifdef XIL_TIMING
  assign CLK_in = CLK_delay ^ IS_CLK_INVERTED_REG;
  assign I_in = I_delay;
  assign RADR0_in = RADR0_delay;
  assign RADR1_in = RADR1_delay;
  assign RADR2_in = RADR2_delay;
  assign RADR3_in = RADR3_delay;
  assign RADR4_in = RADR4_delay;
  assign RADR5_in = RADR5_delay;
  assign WADR0_in = WADR0_delay;
  assign WADR1_in = WADR1_delay;
  assign WADR2_in = WADR2_delay;
  assign WADR3_in = WADR3_delay;
  assign WADR4_in = WADR4_delay;
  assign WE_in = (WE === 1'bz) || WE_delay; // rv 1
`else
  assign CLK_in = CLK ^ IS_CLK_INVERTED_REG;
  assign I_in = I;
  assign RADR0_in = RADR0;
  assign RADR1_in = RADR1;
  assign RADR2_in = RADR2;
  assign RADR3_in = RADR3;
  assign RADR4_in = RADR4;
  assign RADR5_in = RADR5;
  assign WADR0_in = WADR0;
  assign WADR1_in = WADR1;
  assign WADR2_in = WADR2;
  assign WADR3_in = WADR3;
  assign WADR4_in = WADR4;
  assign WE_in = (WE === 1'bz) || WE; // rv 1
`endif

`ifndef XIL_XECLIB
  initial begin
  trig_attr = 1'b0;
  #1;
  trig_attr = ~trig_attr;
end
`endif

`ifndef XIL_TIMING
  initial begin
    $display("Error: [Unisim %s-100] SIMPRIM primitive is not intended for direct instantiation in RTL or functional netlists. This primitive is only available in the SIMPRIM library for implemented netlists, please ensure you are pointing to the correct library. Instance %m", MODULE_NAME);
    #1 $finish;
  end
`endif

`ifdef XIL_TIMING
  reg notifier;
`endif

// begin behavioral model

// end behavioral model

`ifndef XIL_XECLIB
`ifdef XIL_TIMING
  
  wire clk_en_n;
  wire clk_en_p;
  
  assign clk_en_n =  IS_CLK_INVERTED_REG;
  assign clk_en_p = ~IS_CLK_INVERTED_REG;

`endif

  specify
    (CLK => O) = (100:100:100, 100:100:100);
    (RADR0 => O) = (0:0:0, 0:0:0);
    (RADR1 => O) = (0:0:0, 0:0:0);
    (RADR2 => O) = (0:0:0, 0:0:0);
    (RADR3 => O) = (0:0:0, 0:0:0);
    (RADR4 => O) = (0:0:0, 0:0:0);
    (RADR5 => O) = (0:0:0, 0:0:0);
    (WADR0 => O) = (0:0:0, 0:0:0);
    (WADR1 => O) = (0:0:0, 0:0:0);
    (WADR2 => O) = (0:0:0, 0:0:0);
    (WADR3 => O) = (0:0:0, 0:0:0);
    (WADR4 => O) = (0:0:0, 0:0:0);
`ifdef XIL_TIMING
    $period (negedge CLK, 0:0:0, notifier);
    $period (posedge CLK, 0:0:0, notifier);
    $setuphold (negedge CLK, negedge I, 0:0:0, 0:0:0, notifier, clk_en_n, clk_en_n, CLK_delay, I_delay);
    $setuphold (negedge CLK, negedge RADR0, 0:0:0, 0:0:0, notifier, clk_en_n, clk_en_n, CLK_delay, RADR0_delay);
    $setuphold (negedge CLK, negedge RADR1, 0:0:0, 0:0:0, notifier, clk_en_n, clk_en_n, CLK_delay, RADR1_delay);
    $setuphold (negedge CLK, negedge RADR2, 0:0:0, 0:0:0, notifier, clk_en_n, clk_en_n, CLK_delay, RADR2_delay);
    $setuphold (negedge CLK, negedge RADR3, 0:0:0, 0:0:0, notifier, clk_en_n, clk_en_n, CLK_delay, RADR3_delay);
    $setuphold (negedge CLK, negedge RADR4, 0:0:0, 0:0:0, notifier, clk_en_n, clk_en_n, CLK_delay, RADR4_delay);
    $setuphold (negedge CLK, negedge RADR5, 0:0:0, 0:0:0, notifier, clk_en_n, clk_en_n, CLK_delay, RADR5_delay);
    $setuphold (negedge CLK, negedge WADR0, 0:0:0, 0:0:0, notifier, clk_en_n, clk_en_n, CLK_delay, WADR0_delay);
    $setuphold (negedge CLK, negedge WADR1, 0:0:0, 0:0:0, notifier, clk_en_n, clk_en_n, CLK_delay, WADR1_delay);
    $setuphold (negedge CLK, negedge WADR2, 0:0:0, 0:0:0, notifier, clk_en_n, clk_en_n, CLK_delay, WADR2_delay);
    $setuphold (negedge CLK, negedge WADR3, 0:0:0, 0:0:0, notifier, clk_en_n, clk_en_n, CLK_delay, WADR3_delay);
    $setuphold (negedge CLK, negedge WADR4, 0:0:0, 0:0:0, notifier, clk_en_n, clk_en_n, CLK_delay, WADR4_delay);
    $setuphold (negedge CLK, negedge WE, 0:0:0, 0:0:0, notifier, clk_en_n, clk_en_n, CLK_delay, WE_delay);
    $setuphold (negedge CLK, posedge I, 0:0:0, 0:0:0, notifier, clk_en_n, clk_en_n, CLK_delay, I_delay);
    $setuphold (negedge CLK, posedge RADR0, 0:0:0, 0:0:0, notifier, clk_en_n, clk_en_n, CLK_delay, RADR0_delay);
    $setuphold (negedge CLK, posedge RADR1, 0:0:0, 0:0:0, notifier, clk_en_n, clk_en_n, CLK_delay, RADR1_delay);
    $setuphold (negedge CLK, posedge RADR2, 0:0:0, 0:0:0, notifier, clk_en_n, clk_en_n, CLK_delay, RADR2_delay);
    $setuphold (negedge CLK, posedge RADR3, 0:0:0, 0:0:0, notifier, clk_en_n, clk_en_n, CLK_delay, RADR3_delay);
    $setuphold (negedge CLK, posedge RADR4, 0:0:0, 0:0:0, notifier, clk_en_n, clk_en_n, CLK_delay, RADR4_delay);
    $setuphold (negedge CLK, posedge RADR5, 0:0:0, 0:0:0, notifier, clk_en_n, clk_en_n, CLK_delay, RADR5_delay);
    $setuphold (negedge CLK, posedge WADR0, 0:0:0, 0:0:0, notifier, clk_en_n, clk_en_n, CLK_delay, WADR0_delay);
    $setuphold (negedge CLK, posedge WADR1, 0:0:0, 0:0:0, notifier, clk_en_n, clk_en_n, CLK_delay, WADR1_delay);
    $setuphold (negedge CLK, posedge WADR2, 0:0:0, 0:0:0, notifier, clk_en_n, clk_en_n, CLK_delay, WADR2_delay);
    $setuphold (negedge CLK, posedge WADR3, 0:0:0, 0:0:0, notifier, clk_en_n, clk_en_n, CLK_delay, WADR3_delay);
    $setuphold (negedge CLK, posedge WADR4, 0:0:0, 0:0:0, notifier, clk_en_n, clk_en_n, CLK_delay, WADR4_delay);
    $setuphold (negedge CLK, posedge WE, 0:0:0, 0:0:0, notifier, clk_en_n, clk_en_n, CLK_delay, WE_delay);
    $setuphold (posedge CLK, negedge I, 0:0:0, 0:0:0, notifier, clk_en_p, clk_en_p, CLK_delay, I_delay);
    $setuphold (posedge CLK, negedge RADR0, 0:0:0, 0:0:0, notifier, clk_en_p, clk_en_p, CLK_delay, RADR0_delay);
    $setuphold (posedge CLK, negedge RADR1, 0:0:0, 0:0:0, notifier, clk_en_p, clk_en_p, CLK_delay, RADR1_delay);
    $setuphold (posedge CLK, negedge RADR2, 0:0:0, 0:0:0, notifier, clk_en_p, clk_en_p, CLK_delay, RADR2_delay);
    $setuphold (posedge CLK, negedge RADR3, 0:0:0, 0:0:0, notifier, clk_en_p, clk_en_p, CLK_delay, RADR3_delay);
    $setuphold (posedge CLK, negedge RADR4, 0:0:0, 0:0:0, notifier, clk_en_p, clk_en_p, CLK_delay, RADR4_delay);
    $setuphold (posedge CLK, negedge RADR5, 0:0:0, 0:0:0, notifier, clk_en_p, clk_en_p, CLK_delay, RADR5_delay);
    $setuphold (posedge CLK, negedge WADR0, 0:0:0, 0:0:0, notifier, clk_en_p, clk_en_p, CLK_delay, WADR0_delay);
    $setuphold (posedge CLK, negedge WADR1, 0:0:0, 0:0:0, notifier, clk_en_p, clk_en_p, CLK_delay, WADR1_delay);
    $setuphold (posedge CLK, negedge WADR2, 0:0:0, 0:0:0, notifier, clk_en_p, clk_en_p, CLK_delay, WADR2_delay);
    $setuphold (posedge CLK, negedge WADR3, 0:0:0, 0:0:0, notifier, clk_en_p, clk_en_p, CLK_delay, WADR3_delay);
    $setuphold (posedge CLK, negedge WADR4, 0:0:0, 0:0:0, notifier, clk_en_p, clk_en_p, CLK_delay, WADR4_delay);
    $setuphold (posedge CLK, negedge WE, 0:0:0, 0:0:0, notifier, clk_en_p, clk_en_p, CLK_delay, WE_delay);
    $setuphold (posedge CLK, posedge I, 0:0:0, 0:0:0, notifier, clk_en_p, clk_en_p, CLK_delay, I_delay);
    $setuphold (posedge CLK, posedge RADR0, 0:0:0, 0:0:0, notifier, clk_en_p, clk_en_p, CLK_delay, RADR0_delay);
    $setuphold (posedge CLK, posedge RADR1, 0:0:0, 0:0:0, notifier, clk_en_p, clk_en_p, CLK_delay, RADR1_delay);
    $setuphold (posedge CLK, posedge RADR2, 0:0:0, 0:0:0, notifier, clk_en_p, clk_en_p, CLK_delay, RADR2_delay);
    $setuphold (posedge CLK, posedge RADR3, 0:0:0, 0:0:0, notifier, clk_en_p, clk_en_p, CLK_delay, RADR3_delay);
    $setuphold (posedge CLK, posedge RADR4, 0:0:0, 0:0:0, notifier, clk_en_p, clk_en_p, CLK_delay, RADR4_delay);
    $setuphold (posedge CLK, posedge RADR5, 0:0:0, 0:0:0, notifier, clk_en_p, clk_en_p, CLK_delay, RADR5_delay);
    $setuphold (posedge CLK, posedge WADR0, 0:0:0, 0:0:0, notifier, clk_en_p, clk_en_p, CLK_delay, WADR0_delay);
    $setuphold (posedge CLK, posedge WADR1, 0:0:0, 0:0:0, notifier, clk_en_p, clk_en_p, CLK_delay, WADR1_delay);
    $setuphold (posedge CLK, posedge WADR2, 0:0:0, 0:0:0, notifier, clk_en_p, clk_en_p, CLK_delay, WADR2_delay);
    $setuphold (posedge CLK, posedge WADR3, 0:0:0, 0:0:0, notifier, clk_en_p, clk_en_p, CLK_delay, WADR3_delay);
    $setuphold (posedge CLK, posedge WADR4, 0:0:0, 0:0:0, notifier, clk_en_p, clk_en_p, CLK_delay, WADR4_delay);
    $setuphold (posedge CLK, posedge WE, 0:0:0, 0:0:0, notifier, clk_en_p, clk_en_p, CLK_delay, WE_delay);
    $width (negedge CLK, 0:0:0, 0, notifier);
    $width (posedge CLK, 0:0:0, 0, notifier);
`endif
    specparam PATHPULSE$ = 0;
  endspecify
`endif
endmodule

`endcelldefine
