///////////////////////////////////////////////////////////////////////////////
//     Copyright (c) 1995/2016 Xilinx, Inc.
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
// \   \   \/      Version     : 2017.1
//  \   \          Description : Xilinx Timing Simulation Library Component
//  /   /                   Static Dual Port Synchronous RAM 64-Deep by 1-Wide
// /___/   /\      Filename    : RAMD64E.v
// \   \  /  \
//  \___\/\___\
//
///////////////////////////////////////////////////////////////////////////////
// Revision:
//    07/02/10 - Initial version.
//    12/13/11 - 524859 - Added `celldefine and `endcelldefine.
//    03/21/12 - 649330 - Add RAM_ADDRESS_MASK to allow floating WADR6/7.
//    04/16/13 - 683925 - Add invertible pin support.
//    10/22/14 - 808642 - Added #1 to $finish.
// End Revision:
///////////////////////////////////////////////////////////////////////////////

`timescale 1 ps / 1 ps

`celldefine

module RAMD64E #(
`ifdef XIL_TIMING
  parameter LOC = "UNPLACED",
`endif
  parameter [63:0] INIT = 64'h0000000000000000,
  parameter [0:0] IS_CLK_INVERTED = 1'b0,
  parameter [1:0] RAM_ADDRESS_MASK = 2'b00,
  parameter [1:0] RAM_ADDRESS_SPACE = 2'b00
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
  input WADR5,
  input WADR6,
  input WADR7,
  input WE
);
  
// define constants
  localparam MODULE_NAME = "RAMD64E";

  reg trig_attr = 1'b0;
// include dynamic registers - XILINX test only
`ifdef XIL_DR
  `include "RAMD64E_dr.v"
`else
  reg [63:0] INIT_REG = INIT;
  reg [0:0] IS_CLK_INVERTED_REG = IS_CLK_INVERTED;
  reg [1:0] RAM_ADDRESS_MASK_REG = RAM_ADDRESS_MASK;
  reg [1:0] RAM_ADDRESS_SPACE_REG = RAM_ADDRESS_SPACE;
`endif

`ifdef XIL_XECLIB
  wire IS_CLK_INVERTED_BIN;
`else
  reg IS_CLK_INVERTED_BIN;
`endif

`ifdef XIL_ATTR_TEST
  reg attr_test = 1'b1;
`else
  reg attr_test = 1'b0;
`endif
  reg attr_err = 1'b0;

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
  wire WADR5_in;
  wire WADR6_in;
  wire WADR7_in;
  wire WE_in;

`ifdef XIL_TIMING
  wire CLK_delay;
  wire I_delay;
  wire WADR0_delay;
  wire WADR1_delay;
  wire WADR2_delay;
  wire WADR3_delay;
  wire WADR4_delay;
  wire WADR5_delay;
  wire WADR6_delay;
  wire WADR7_delay;
  wire WE_delay;
`endif

`ifdef XIL_TIMING
  assign CLK_in = CLK_delay ^ IS_CLK_INVERTED_BIN;
  assign I_in = I_delay;
  assign WADR0_in = WADR0_delay;
  assign WADR1_in = WADR1_delay;
  assign WADR2_in = WADR2_delay;
  assign WADR3_in = WADR3_delay;
  assign WADR4_in = WADR4_delay;
  assign WADR5_in = WADR5_delay;
  assign WADR6_in = WADR6_delay;
  assign WADR7_in = WADR7_delay;
  assign WE_in = (WE === 1'bz) || WE_delay; // rv 1
`else
  assign CLK_in = CLK ^ IS_CLK_INVERTED_BIN;
  assign I_in = I;
  assign WADR0_in = WADR0;
  assign WADR1_in = WADR1;
  assign WADR2_in = WADR2;
  assign WADR3_in = WADR3;
  assign WADR4_in = WADR4;
  assign WADR5_in = WADR5;
  assign WADR6_in = WADR6;
  assign WADR7_in = WADR7;
  assign WE_in = (WE === 1'bz) || WE; // rv 1
`endif
  assign RADR0_in = RADR0;
  assign RADR1_in = RADR1;
  assign RADR2_in = RADR2;
  assign RADR3_in = RADR3;
  assign RADR4_in = RADR4;
  assign RADR5_in = RADR5;

`ifndef XIL_XECLIB
  initial begin
    #1;
    trig_attr = ~trig_attr;
  end
`endif

`ifdef XIL_XECLIB
  assign IS_CLK_INVERTED_BIN = IS_CLK_INVERTED_REG;

`else
  always @ (trig_attr) begin
  #1;
  IS_CLK_INVERTED_BIN = IS_CLK_INVERTED_REG;

  end
`endif

`ifndef XIL_TIMING
  initial begin
    $display("Error: [Unisim %s-101] SIMPRIM primitive is not intended for direct instantiation in RTL or functional netlists. This primitive is only available in the SIMPRIM library for implemented netlists, please ensure you are pointing to the correct library. Instance %m", MODULE_NAME);
    #1 $finish;
  end
`endif

`ifdef XIL_TIMING
  reg notifier;
`endif

// begin behavioral model

  reg [63:0] mem;
  reg O_out;

  assign O = O_out;

`ifndef XIL_XECLIB
  initial begin
    mem = INIT;
    O_out = mem[{RADR5_in,RADR4_in,RADR3_in,RADR2_in,RADR1_in,RADR0_in}];
  end
`endif

  always @(posedge CLK_in)
    if (WE_in == 1'b1 &&
        (RAM_ADDRESS_MASK_REG[1] || WADR7_in == RAM_ADDRESS_SPACE_REG[1]) &&
        (RAM_ADDRESS_MASK_REG[0] || WADR6_in == RAM_ADDRESS_SPACE_REG[0]) ) begin
      mem[{WADR5_in,WADR4_in,WADR3_in,WADR2_in,WADR1_in,WADR0_in}] = I_in;
     end

  always @ (*) begin
    O_out = mem[{RADR5_in,RADR4_in,RADR3_in,RADR2_in,RADR1_in,RADR0_in}];
  end

`ifdef XIL_TIMING
  always @(notifier) mem[{WADR5_in,WADR4_in,WADR3_in,WADR2_in,WADR1_in,WADR0_in}] = 1'bx;
`endif

// end behavioral model

`ifndef XIL_XECLIB
`ifdef XIL_TIMING

  wire clk_en_n;
  wire clk_en_p;

  assign clk_en_n = IS_CLK_INVERTED_BIN;
  assign clk_en_p = ~IS_CLK_INVERTED_BIN;

  wire we_clk_en_n;
  wire we_clk_en_p;

  assign we_clk_en_n = WE_in && IS_CLK_INVERTED_BIN;
  assign we_clk_en_p = WE_in && ~IS_CLK_INVERTED_BIN;
`endif

  specify
    (CLK => O) = (100:100:100, 100:100:100);
    (RADR0 => O) = (0:0:0, 0:0:0);
    (RADR1 => O) = (0:0:0, 0:0:0);
    (RADR2 => O) = (0:0:0, 0:0:0);
    (RADR3 => O) = (0:0:0, 0:0:0);
    (RADR4 => O) = (0:0:0, 0:0:0);
    (RADR5 => O) = (0:0:0, 0:0:0);
`ifdef XIL_TIMING
    $period (negedge CLK &&& WE, 0:0:0, notifier);
    $period (posedge CLK &&& WE, 0:0:0, notifier);
    $setuphold (negedge CLK, negedge I, 0:0:0, 0:0:0, notifier, we_clk_en_n, we_clk_en_n, CLK_delay, I_delay);
    $setuphold (negedge CLK, negedge WADR0, 0:0:0, 0:0:0, notifier, we_clk_en_n, we_clk_en_n, CLK_delay, WADR0_delay);
    $setuphold (negedge CLK, negedge WADR1, 0:0:0, 0:0:0, notifier, we_clk_en_n, we_clk_en_n, CLK_delay, WADR1_delay);
    $setuphold (negedge CLK, negedge WADR2, 0:0:0, 0:0:0, notifier, we_clk_en_n, we_clk_en_n, CLK_delay, WADR2_delay);
    $setuphold (negedge CLK, negedge WADR3, 0:0:0, 0:0:0, notifier, we_clk_en_n, we_clk_en_n, CLK_delay, WADR3_delay);
    $setuphold (negedge CLK, negedge WADR4, 0:0:0, 0:0:0, notifier, we_clk_en_n, we_clk_en_n, CLK_delay, WADR4_delay);
    $setuphold (negedge CLK, negedge WADR5, 0:0:0, 0:0:0, notifier, we_clk_en_n, we_clk_en_n, CLK_delay, WADR5_delay);
    $setuphold (negedge CLK, negedge WADR6, 0:0:0, 0:0:0, notifier, we_clk_en_n, we_clk_en_n, CLK_delay, WADR6_delay);
    $setuphold (negedge CLK, negedge WADR7, 0:0:0, 0:0:0, notifier, we_clk_en_n, we_clk_en_n, CLK_delay, WADR7_delay);
    $setuphold (negedge CLK, negedge WE, 0:0:0, 0:0:0, notifier, clk_en_n, clk_en_n, CLK_delay, WE_delay);
    $setuphold (negedge CLK, posedge I, 0:0:0, 0:0:0, notifier, we_clk_en_n, we_clk_en_n, CLK_delay, I_delay);
    $setuphold (negedge CLK, posedge WADR0, 0:0:0, 0:0:0, notifier, we_clk_en_n, we_clk_en_n, CLK_delay, WADR0_delay);
    $setuphold (negedge CLK, posedge WADR1, 0:0:0, 0:0:0, notifier, we_clk_en_n, we_clk_en_n, CLK_delay, WADR1_delay);
    $setuphold (negedge CLK, posedge WADR2, 0:0:0, 0:0:0, notifier, we_clk_en_n, we_clk_en_n, CLK_delay, WADR2_delay);
    $setuphold (negedge CLK, posedge WADR3, 0:0:0, 0:0:0, notifier, we_clk_en_n, we_clk_en_n, CLK_delay, WADR3_delay);
    $setuphold (negedge CLK, posedge WADR4, 0:0:0, 0:0:0, notifier, we_clk_en_n, we_clk_en_n, CLK_delay, WADR4_delay);
    $setuphold (negedge CLK, posedge WADR5, 0:0:0, 0:0:0, notifier, we_clk_en_n, we_clk_en_n, CLK_delay, WADR5_delay);
    $setuphold (negedge CLK, posedge WADR6, 0:0:0, 0:0:0, notifier, we_clk_en_n, we_clk_en_n, CLK_delay, WADR6_delay);
    $setuphold (negedge CLK, posedge WADR7, 0:0:0, 0:0:0, notifier, we_clk_en_n, we_clk_en_n, CLK_delay, WADR7_delay);
    $setuphold (negedge CLK, posedge WE, 0:0:0, 0:0:0, notifier, clk_en_n, clk_en_n, CLK_delay, WE_delay);
    $setuphold (posedge CLK, negedge I, 0:0:0, 0:0:0, notifier, we_clk_en_p, we_clk_en_p, CLK_delay, I_delay);
    $setuphold (posedge CLK, negedge WADR0, 0:0:0, 0:0:0, notifier, we_clk_en_p, we_clk_en_p, CLK_delay, WADR0_delay);
    $setuphold (posedge CLK, negedge WADR1, 0:0:0, 0:0:0, notifier, we_clk_en_p, we_clk_en_p, CLK_delay, WADR1_delay);
    $setuphold (posedge CLK, negedge WADR2, 0:0:0, 0:0:0, notifier, we_clk_en_p, we_clk_en_p, CLK_delay, WADR2_delay);
    $setuphold (posedge CLK, negedge WADR3, 0:0:0, 0:0:0, notifier, we_clk_en_p, we_clk_en_p, CLK_delay, WADR3_delay);
    $setuphold (posedge CLK, negedge WADR4, 0:0:0, 0:0:0, notifier, we_clk_en_p, we_clk_en_p, CLK_delay, WADR4_delay);
    $setuphold (posedge CLK, negedge WADR5, 0:0:0, 0:0:0, notifier, we_clk_en_p, we_clk_en_p, CLK_delay, WADR5_delay);
    $setuphold (posedge CLK, negedge WADR6, 0:0:0, 0:0:0, notifier, we_clk_en_p, we_clk_en_p, CLK_delay, WADR6_delay);
    $setuphold (posedge CLK, negedge WADR7, 0:0:0, 0:0:0, notifier, we_clk_en_p, we_clk_en_p, CLK_delay, WADR7_delay);
    $setuphold (posedge CLK, negedge WE, 0:0:0, 0:0:0, notifier, clk_en_p, clk_en_p, CLK_delay, WE_delay);
    $setuphold (posedge CLK, posedge I, 0:0:0, 0:0:0, notifier, we_clk_en_p, we_clk_en_p, CLK_delay, I_delay);
    $setuphold (posedge CLK, posedge WADR0, 0:0:0, 0:0:0, notifier, we_clk_en_p, we_clk_en_p, CLK_delay, WADR0_delay);
    $setuphold (posedge CLK, posedge WADR1, 0:0:0, 0:0:0, notifier, we_clk_en_p, we_clk_en_p, CLK_delay, WADR1_delay);
    $setuphold (posedge CLK, posedge WADR2, 0:0:0, 0:0:0, notifier, we_clk_en_p, we_clk_en_p, CLK_delay, WADR2_delay);
    $setuphold (posedge CLK, posedge WADR3, 0:0:0, 0:0:0, notifier, we_clk_en_p, we_clk_en_p, CLK_delay, WADR3_delay);
    $setuphold (posedge CLK, posedge WADR4, 0:0:0, 0:0:0, notifier, we_clk_en_p, we_clk_en_p, CLK_delay, WADR4_delay);
    $setuphold (posedge CLK, posedge WADR5, 0:0:0, 0:0:0, notifier, we_clk_en_p, we_clk_en_p, CLK_delay, WADR5_delay);
    $setuphold (posedge CLK, posedge WADR6, 0:0:0, 0:0:0, notifier, we_clk_en_p, we_clk_en_p, CLK_delay, WADR6_delay);
    $setuphold (posedge CLK, posedge WADR7, 0:0:0, 0:0:0, notifier, we_clk_en_p, we_clk_en_p, CLK_delay, WADR7_delay);
    $setuphold (posedge CLK, posedge WE, 0:0:0, 0:0:0, notifier, clk_en_p, clk_en_p, CLK_delay, WE_delay);
    $width (negedge CLK, 0:0:0, 0, notifier);
    $width (posedge CLK, 0:0:0, 0, notifier);
`endif
    specparam PATHPULSE$ = 0;
  endspecify
`endif

endmodule

`endcelldefine
