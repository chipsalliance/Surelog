///////////////////////////////////////////////////////////////////////////////
//     Copyright (c) 1995/2015 Xilinx, Inc.
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
// \   \   \/      Version     : 2016.1
//  \   \          Description : Xilinx Unified Simulation Library Component
//  /   /                        Metastability Hardened Registers
// /___/   /\      Filename    : HARD_SYNC.v
// \   \  /  \
//  \___\/\___\
//
///////////////////////////////////////////////////////////////////////////////
//  Revision:
//  01/30/13 Initial version
//  05/08/13 712367 - fix blocking assignments
//  05/17/13 718960 - fix BIN encoding
//  05/17/13 719092 - remove SR, add IS_CLK_INVERTED
//  10/22/14 808642 - Added #1 to $finish
//  End Revision:
///////////////////////////////////////////////////////////////////////////////

`timescale 1 ps / 1 ps

`celldefine

module HARD_SYNC #(
`ifdef XIL_TIMING
  parameter LOC = "UNPLACED",
`endif
  parameter [0:0] INIT = 1'b0,
  parameter [0:0] IS_CLK_INVERTED = 1'b0,
  parameter integer LATENCY = 2
)(
  output DOUT,

  input CLK,
  input DIN
);
  
// define constants
  localparam MODULE_NAME = "HARD_SYNC";

// Parameter encodings and registers
  localparam LATENCY_2 = 0;
  localparam LATENCY_3 = 1;

  reg trig_attr = 1'b0;
// include dynamic registers - XILINX test only
`ifdef XIL_DR
  `include "HARD_SYNC_dr.v"
`else
  localparam [0:0] INIT_REG = INIT;
  localparam [0:0] IS_CLK_INVERTED_REG = IS_CLK_INVERTED;
  localparam [1:0] LATENCY_REG = LATENCY;
`endif

  wire INIT_BIN;
  wire IS_CLK_INVERTED_BIN;
  wire LATENCY_BIN;

`ifdef XIL_XECLIB
  tri0 glblGSR = 1'b0;
`else
  `ifdef XIL_ATTR_TEST
  reg attr_test = 1'b1;
  `else
  reg attr_test = 1'b0;
  `endif
  reg attr_err = 1'b0;
  tri0 glblGSR = glbl.GSR;
`endif

  wire CLK_in;
  wire DIN_in;

`ifdef XIL_TIMING
  wire CLK_delay;
  wire DIN_delay;
`ifdef XIL_XECLIB
  assign CLK_delay = CLK;
  assign DIN_delay = DIN;
`endif
`endif

`ifdef XIL_TIMING
  assign CLK_in = CLK_delay ^ IS_CLK_INVERTED_BIN;
  assign DIN_in = DIN_delay;
`else
  assign CLK_in = CLK ^ IS_CLK_INVERTED_BIN;
  assign DIN_in = DIN;
`endif

  assign INIT_BIN = INIT_REG;

  assign IS_CLK_INVERTED_BIN = IS_CLK_INVERTED_REG;

  assign LATENCY_BIN =
    (LATENCY_REG == 2) ? LATENCY_2 :
    (LATENCY_REG == 3) ? LATENCY_3 :
     LATENCY_2;

`ifndef XIL_XECLIB
  initial begin
    #1;
    trig_attr = ~trig_attr;
  end

  always @ (trig_attr) begin
  #1;
    if ((attr_test == 1'b1) ||
        ((LATENCY_REG != 2) &&
         (LATENCY_REG != 3))) begin
      $display("Error: [Unisim %s-103] LATENCY attribute is set to %d.  Legal values for this attribute are 2 or 3. Instance: %m", MODULE_NAME, LATENCY_REG);
      attr_err = 1'b1;
    end

    if (attr_err == 1'b1) #1 $finish;
  end
`endif

reg [2:0] DIN_reg;

assign DOUT = (LATENCY_BIN == LATENCY_3) && DIN_reg[2] || (LATENCY_BIN == LATENCY_2) && DIN_reg[1];

always @ (posedge CLK_in or posedge glblGSR) begin
   if (glblGSR == 1'b1) begin
      DIN_reg <= {INIT_BIN, INIT_BIN, INIT_BIN};
      end
   else begin
      DIN_reg <= {DIN_reg[1:0], DIN_in};
      end
   end

`ifndef XIL_XECLIB
`ifdef XIL_TIMING
  reg notifier;

  wire clk_en_n;
  wire clk_en_p;

  assign clk_en_n = IS_CLK_INVERTED_BIN;
  assign clk_en_p = ~IS_CLK_INVERTED_BIN;
`endif

  specify
    (CLK => DOUT) = (100:100:100, 100:100:100);
`ifdef XIL_TIMING
    $period (negedge CLK, 0:0:0, notifier);
    $period (posedge CLK, 0:0:0, notifier);
    $setuphold (negedge CLK, negedge DIN, 0:0:0, 0:0:0, notifier,clk_en_n,clk_en_n, CLK_delay, DIN_delay);
    $setuphold (negedge CLK, posedge DIN, 0:0:0, 0:0:0, notifier,clk_en_n,clk_en_n, CLK_delay, DIN_delay);
    $setuphold (posedge CLK, negedge DIN, 0:0:0, 0:0:0, notifier,clk_en_p,clk_en_p, CLK_delay, DIN_delay);
    $setuphold (posedge CLK, posedge DIN, 0:0:0, 0:0:0, notifier,clk_en_p,clk_en_p, CLK_delay, DIN_delay);
    $width (negedge CLK, 0:0:0, 0, notifier);
    $width (posedge CLK, 0:0:0, 0, notifier);
`endif
    specparam PATHPULSE$ = 0;
  endspecify
`endif

endmodule

`endcelldefine
