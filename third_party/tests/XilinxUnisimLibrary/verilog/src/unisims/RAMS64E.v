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
//  /   /                   Static Single Port Synchronous RAM 64-Deep by 1-Wide
// /___/   /\      Filename    : RAMS64E.v
// \   \  /  \
//  \___\/\___\
//
///////////////////////////////////////////////////////////////////////////////
// Revision:
//    07/02/10 - Initial version.
//    12/13/11 - 524859 - Added `celldefine and `endcelldefine.
//    03/21/12 - 649330 - Add RAM_ADDRESS_MASK to allow floating WADR6/7.
//    04/16/13 - 683925 - add invertible pin support.
//    10/22/14 - 808642 - Added #1 to $finish.
// End Revision:
///////////////////////////////////////////////////////////////////////////////

`timescale 1 ps / 1 ps

`celldefine

module RAMS64E #(
`ifdef XIL_TIMING
  parameter LOC = "UNPLACED",
`endif
  parameter [63:0] INIT = 64'h0000000000000000,
  parameter [0:0] IS_CLK_INVERTED = 1'b0,
  parameter [1:0] RAM_ADDRESS_MASK = 2'b00,
  parameter [1:0] RAM_ADDRESS_SPACE = 2'b00
)(
  output O,

  input ADR0,
  input ADR1,
  input ADR2,
  input ADR3,
  input ADR4,
  input ADR5,
  input CLK,
  input I,
  input WADR6,
  input WADR7,
  input WE
);
  
// define constants
  localparam MODULE_NAME = "RAMS64E";

  reg trig_attr = 1'b0;
// include dynamic registers - XILINX test only
`ifdef XIL_DR
  `include "RAMS64E_dr.v"
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

  wire ADR0_in;
  wire ADR1_in;
  wire ADR2_in;
  wire ADR3_in;
  wire ADR4_in;
  wire ADR5_in;
  wire CLK_in;
  wire I_in;
  wire WADR6_in;
  wire WADR7_in;
  wire WE_in;

`ifdef XIL_TIMING
  wire ADR0_delay;
  wire ADR1_delay;
  wire ADR2_delay;
  wire ADR3_delay;
  wire ADR4_delay;
  wire ADR5_delay;
  wire CLK_delay;
  wire I_delay;
  wire WADR6_delay;
  wire WADR7_delay;
  wire WE_delay;
`endif

`ifdef XIL_TIMING
  assign ADR0_in = ADR0_delay;
  assign ADR1_in = ADR1_delay;
  assign ADR2_in = ADR2_delay;
  assign ADR3_in = ADR3_delay;
  assign ADR4_in = ADR4_delay;
  assign ADR5_in = ADR5_delay;
  assign CLK_in = CLK_delay ^ IS_CLK_INVERTED_BIN;
  assign I_in = I_delay;
  assign WADR6_in = WADR6_delay;
  assign WADR7_in = WADR7_delay;
  assign WE_in = (WE === 1'bz) || WE_delay; // rv 1
`else
  assign ADR0_in = ADR0;
  assign ADR1_in = ADR1;
  assign ADR2_in = ADR2;
  assign ADR3_in = ADR3;
  assign ADR4_in = ADR4;
  assign ADR5_in = ADR5;
  assign CLK_in = CLK ^ IS_CLK_INVERTED_BIN;
  assign I_in = I;
  assign WADR6_in = WADR6;
  assign WADR7_in = WADR7;
  assign WE_in = (WE === 1'bz) || WE; // rv 1
`endif

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
    O_out = mem[{ADR5_in, ADR4_in, ADR3_in, ADR2_in, ADR1_in, ADR0_in}];
  end
`endif

  always @(posedge CLK_in)
    if (WE_in == 1'b1 &&
        (RAM_ADDRESS_MASK_REG[1] || WADR7_in == RAM_ADDRESS_SPACE_REG[1]) &&
        (RAM_ADDRESS_MASK_REG[0] || WADR6_in == RAM_ADDRESS_SPACE_REG[0]) ) begin
      mem[{ADR5_in, ADR4_in, ADR3_in, ADR2_in, ADR1_in, ADR0_in}] = I_in;
    end

   always @ (*) begin
     O_out = mem[{ADR5_in, ADR4_in, ADR3_in, ADR2_in, ADR1_in, ADR0_in}];
   end

`ifdef XIL_TIMING
  always @(notifier) mem[{ADR5_in, ADR4_in, ADR3_in, ADR2_in, ADR1_in, ADR0_in}] <= 1'bx;
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
    (ADR0 => O) = (0:0:0, 0:0:0);
    (ADR1 => O) = (0:0:0, 0:0:0);
    (ADR2 => O) = (0:0:0, 0:0:0);
    (ADR3 => O) = (0:0:0, 0:0:0);
    (ADR4 => O) = (0:0:0, 0:0:0);
    (ADR5 => O) = (0:0:0, 0:0:0);
    (CLK => O) = (100:100:100, 100:100:100);
`ifdef XIL_TIMING
    $period (negedge CLK &&& WE, 0:0:0, notifier);
    $period (posedge CLK &&& WE, 0:0:0, notifier);
    $setuphold (negedge CLK, negedge ADR0, 0:0:0, 0:0:0, notifier, we_clk_en_n, we_clk_en_n, CLK_delay, ADR0_delay);
    $setuphold (negedge CLK, negedge ADR1, 0:0:0, 0:0:0, notifier, we_clk_en_n, we_clk_en_n, CLK_delay, ADR1_delay);
    $setuphold (negedge CLK, negedge ADR2, 0:0:0, 0:0:0, notifier, we_clk_en_n, we_clk_en_n, CLK_delay, ADR2_delay);
    $setuphold (negedge CLK, negedge ADR3, 0:0:0, 0:0:0, notifier, we_clk_en_n, we_clk_en_n, CLK_delay, ADR3_delay);
    $setuphold (negedge CLK, negedge ADR4, 0:0:0, 0:0:0, notifier, we_clk_en_n, we_clk_en_n, CLK_delay, ADR4_delay);
    $setuphold (negedge CLK, negedge ADR5, 0:0:0, 0:0:0, notifier, we_clk_en_n, we_clk_en_n, CLK_delay, ADR5_delay);
    $setuphold (negedge CLK, negedge I, 0:0:0, 0:0:0, notifier, we_clk_en_n, we_clk_en_n, CLK_delay, I_delay);
    $setuphold (negedge CLK, negedge WADR6, 0:0:0, 0:0:0, notifier, we_clk_en_n, we_clk_en_n, CLK_delay, WADR6_delay);
    $setuphold (negedge CLK, negedge WADR7, 0:0:0, 0:0:0, notifier, we_clk_en_n, we_clk_en_n, CLK_delay, WADR7_delay);
    $setuphold (negedge CLK, negedge WE, 0:0:0, 0:0:0, notifier, clk_en_n, clk_en_n, CLK_delay, WE_delay);
    $setuphold (negedge CLK, posedge ADR0, 0:0:0, 0:0:0, notifier, we_clk_en_n, we_clk_en_n, CLK_delay, ADR0_delay);
    $setuphold (negedge CLK, posedge ADR1, 0:0:0, 0:0:0, notifier, we_clk_en_n, we_clk_en_n, CLK_delay, ADR1_delay);
    $setuphold (negedge CLK, posedge ADR2, 0:0:0, 0:0:0, notifier, we_clk_en_n, we_clk_en_n, CLK_delay, ADR2_delay);
    $setuphold (negedge CLK, posedge ADR3, 0:0:0, 0:0:0, notifier, we_clk_en_n, we_clk_en_n, CLK_delay, ADR3_delay);
    $setuphold (negedge CLK, posedge ADR4, 0:0:0, 0:0:0, notifier, we_clk_en_n, we_clk_en_n, CLK_delay, ADR4_delay);
    $setuphold (negedge CLK, posedge ADR5, 0:0:0, 0:0:0, notifier, we_clk_en_n, we_clk_en_n, CLK_delay, ADR5_delay);
    $setuphold (negedge CLK, posedge I, 0:0:0, 0:0:0, notifier, we_clk_en_n, we_clk_en_n, CLK_delay, I_delay);
    $setuphold (negedge CLK, posedge WADR6, 0:0:0, 0:0:0, notifier, we_clk_en_n, we_clk_en_n, CLK_delay, WADR6_delay);
    $setuphold (negedge CLK, posedge WADR7, 0:0:0, 0:0:0, notifier, we_clk_en_n, we_clk_en_n, CLK_delay, WADR7_delay);
    $setuphold (negedge CLK, posedge WE, 0:0:0, 0:0:0, notifier, clk_en_n, clk_en_n, CLK_delay, WE_delay);
    $setuphold (posedge CLK, negedge ADR0, 0:0:0, 0:0:0, notifier, we_clk_en_p, we_clk_en_p, CLK_delay, ADR0_delay);
    $setuphold (posedge CLK, negedge ADR1, 0:0:0, 0:0:0, notifier, we_clk_en_p, we_clk_en_p, CLK_delay, ADR1_delay);
    $setuphold (posedge CLK, negedge ADR2, 0:0:0, 0:0:0, notifier, we_clk_en_p, we_clk_en_p, CLK_delay, ADR2_delay);
    $setuphold (posedge CLK, negedge ADR3, 0:0:0, 0:0:0, notifier, we_clk_en_p, we_clk_en_p, CLK_delay, ADR3_delay);
    $setuphold (posedge CLK, negedge ADR4, 0:0:0, 0:0:0, notifier, we_clk_en_p, we_clk_en_p, CLK_delay, ADR4_delay);
    $setuphold (posedge CLK, negedge ADR5, 0:0:0, 0:0:0, notifier, we_clk_en_p, we_clk_en_p, CLK_delay, ADR5_delay);
    $setuphold (posedge CLK, negedge I, 0:0:0, 0:0:0, notifier, we_clk_en_p, we_clk_en_p, CLK_delay, I_delay);
    $setuphold (posedge CLK, negedge WADR6, 0:0:0, 0:0:0, notifier, we_clk_en_p, we_clk_en_p, CLK_delay, WADR6_delay);
    $setuphold (posedge CLK, negedge WADR7, 0:0:0, 0:0:0, notifier, we_clk_en_p, we_clk_en_p, CLK_delay, WADR7_delay);
    $setuphold (posedge CLK, negedge WE, 0:0:0, 0:0:0, notifier, clk_en_p, clk_en_p, CLK_delay, WE_delay);
    $setuphold (posedge CLK, posedge ADR0, 0:0:0, 0:0:0, notifier, we_clk_en_p, we_clk_en_p, CLK_delay, ADR0_delay);
    $setuphold (posedge CLK, posedge ADR1, 0:0:0, 0:0:0, notifier, we_clk_en_p, we_clk_en_p, CLK_delay, ADR1_delay);
    $setuphold (posedge CLK, posedge ADR2, 0:0:0, 0:0:0, notifier, we_clk_en_p, we_clk_en_p, CLK_delay, ADR2_delay);
    $setuphold (posedge CLK, posedge ADR3, 0:0:0, 0:0:0, notifier, we_clk_en_p, we_clk_en_p, CLK_delay, ADR3_delay);
    $setuphold (posedge CLK, posedge ADR4, 0:0:0, 0:0:0, notifier, we_clk_en_p, we_clk_en_p, CLK_delay, ADR4_delay);
    $setuphold (posedge CLK, posedge ADR5, 0:0:0, 0:0:0, notifier, we_clk_en_p, we_clk_en_p, CLK_delay, ADR5_delay);
    $setuphold (posedge CLK, posedge I, 0:0:0, 0:0:0, notifier, we_clk_en_p, we_clk_en_p, CLK_delay, I_delay);
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
