///////////////////////////////////////////////////////////////////////////////
//     Copyright (c) 1995/2018 Xilinx, Inc.
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
// \   \   \/      Version     : 2018.3
//  \   \          Description : Xilinx Unified Simulation Library Component
//  /   /                        DSP_C_DATA
// /___/   /\      Filename    : DSP_C_DATA.v
// \   \  /  \
//  \___\/\___\
//
///////////////////////////////////////////////////////////////////////////////
//  Revision:
//  07/15/12 - Migrate from E1.
//  12/10/12 - Add dynamic registers
//  04/23/13 - 714772 - remove sensitivity to negedge GSR
//  10/22/14 - 808642 - Added #1 to $finish
//  End Revision:
///////////////////////////////////////////////////////////////////////////////

`timescale 1 ps / 1 ps

`celldefine

module DSP_C_DATA #(
`ifdef XIL_TIMING
  parameter LOC = "UNPLACED",
`endif
  parameter integer CREG = 1,
  parameter [0:0] IS_CLK_INVERTED = 1'b0,
  parameter [0:0] IS_RSTC_INVERTED = 1'b0
)(
  output [47:0] C_DATA,

  input [47:0] C,
  input CEC,
  input CLK,
  input RSTC
);
  
// define constants
  localparam MODULE_NAME = "DSP_C_DATA";

  reg trig_attr;
// include dynamic registers - XILINX test only
`ifdef XIL_DR
  `include "DSP_C_DATA_dr.v"
`else
  reg [31:0] CREG_REG = CREG;
  reg [0:0] IS_CLK_INVERTED_REG = IS_CLK_INVERTED;
  reg [0:0] IS_RSTC_INVERTED_REG = IS_RSTC_INVERTED;
`endif

`ifdef XIL_XECLIB
  wire CREG_BIN;
`else
  reg CREG_BIN;
`endif

`ifdef XIL_XECLIB
  reg glblGSR = 1'b0;
`else
  tri0 glblGSR = glbl.GSR;
`endif

  wire CEC_in;
  wire CLK_in;
  wire RSTC_in;
  wire [47:0] C_in;

`ifdef XIL_TIMING
  wire CEC_delay;
  wire CLK_delay;
  wire RSTC_delay;
  wire [47:0] C_delay;
`endif
  
`ifdef XIL_TIMING
  assign CEC_in = (CEC !== 1'bz) && CEC_delay; // rv 0
  assign CLK_in = (CLK !== 1'bz) && (CLK_delay ^ IS_CLK_INVERTED_REG); // rv 0
  assign C_in[0] = (C[0] === 1'bz) || C_delay[0]; // rv 1
  assign C_in[10] = (C[10] === 1'bz) || C_delay[10]; // rv 1
  assign C_in[11] = (C[11] === 1'bz) || C_delay[11]; // rv 1
  assign C_in[12] = (C[12] === 1'bz) || C_delay[12]; // rv 1
  assign C_in[13] = (C[13] === 1'bz) || C_delay[13]; // rv 1
  assign C_in[14] = (C[14] === 1'bz) || C_delay[14]; // rv 1
  assign C_in[15] = (C[15] === 1'bz) || C_delay[15]; // rv 1
  assign C_in[16] = (C[16] === 1'bz) || C_delay[16]; // rv 1
  assign C_in[17] = (C[17] === 1'bz) || C_delay[17]; // rv 1
  assign C_in[18] = (C[18] === 1'bz) || C_delay[18]; // rv 1
  assign C_in[19] = (C[19] === 1'bz) || C_delay[19]; // rv 1
  assign C_in[1] = (C[1] === 1'bz) || C_delay[1]; // rv 1
  assign C_in[20] = (C[20] === 1'bz) || C_delay[20]; // rv 1
  assign C_in[21] = (C[21] === 1'bz) || C_delay[21]; // rv 1
  assign C_in[22] = (C[22] === 1'bz) || C_delay[22]; // rv 1
  assign C_in[23] = (C[23] === 1'bz) || C_delay[23]; // rv 1
  assign C_in[24] = (C[24] === 1'bz) || C_delay[24]; // rv 1
  assign C_in[25] = (C[25] === 1'bz) || C_delay[25]; // rv 1
  assign C_in[26] = (C[26] === 1'bz) || C_delay[26]; // rv 1
  assign C_in[27] = (C[27] === 1'bz) || C_delay[27]; // rv 1
  assign C_in[28] = (C[28] === 1'bz) || C_delay[28]; // rv 1
  assign C_in[29] = (C[29] === 1'bz) || C_delay[29]; // rv 1
  assign C_in[2] = (C[2] === 1'bz) || C_delay[2]; // rv 1
  assign C_in[30] = (C[30] === 1'bz) || C_delay[30]; // rv 1
  assign C_in[31] = (C[31] === 1'bz) || C_delay[31]; // rv 1
  assign C_in[32] = (C[32] === 1'bz) || C_delay[32]; // rv 1
  assign C_in[33] = (C[33] === 1'bz) || C_delay[33]; // rv 1
  assign C_in[34] = (C[34] === 1'bz) || C_delay[34]; // rv 1
  assign C_in[35] = (C[35] === 1'bz) || C_delay[35]; // rv 1
  assign C_in[36] = (C[36] === 1'bz) || C_delay[36]; // rv 1
  assign C_in[37] = (C[37] === 1'bz) || C_delay[37]; // rv 1
  assign C_in[38] = (C[38] === 1'bz) || C_delay[38]; // rv 1
  assign C_in[39] = (C[39] === 1'bz) || C_delay[39]; // rv 1
  assign C_in[3] = (C[3] === 1'bz) || C_delay[3]; // rv 1
  assign C_in[40] = (C[40] === 1'bz) || C_delay[40]; // rv 1
  assign C_in[41] = (C[41] === 1'bz) || C_delay[41]; // rv 1
  assign C_in[42] = (C[42] === 1'bz) || C_delay[42]; // rv 1
  assign C_in[43] = (C[43] === 1'bz) || C_delay[43]; // rv 1
  assign C_in[44] = (C[44] === 1'bz) || C_delay[44]; // rv 1
  assign C_in[45] = (C[45] === 1'bz) || C_delay[45]; // rv 1
  assign C_in[46] = (C[46] === 1'bz) || C_delay[46]; // rv 1
  assign C_in[47] = (C[47] === 1'bz) || C_delay[47]; // rv 1
  assign C_in[4] = (C[4] === 1'bz) || C_delay[4]; // rv 1
  assign C_in[5] = (C[5] === 1'bz) || C_delay[5]; // rv 1
  assign C_in[6] = (C[6] === 1'bz) || C_delay[6]; // rv 1
  assign C_in[7] = (C[7] === 1'bz) || C_delay[7]; // rv 1
  assign C_in[8] = (C[8] === 1'bz) || C_delay[8]; // rv 1
  assign C_in[9] = (C[9] === 1'bz) || C_delay[9]; // rv 1
  assign RSTC_in = (RSTC !== 1'bz) && (RSTC_delay ^ IS_RSTC_INVERTED_REG); // rv 0
`else
  assign CEC_in = (CEC !== 1'bz) && CEC; // rv 0
  assign CLK_in = (CLK !== 1'bz) && (CLK ^ IS_CLK_INVERTED_REG); // rv 0
  assign C_in[0] = (C[0] === 1'bz) || C[0]; // rv 1
  assign C_in[10] = (C[10] === 1'bz) || C[10]; // rv 1
  assign C_in[11] = (C[11] === 1'bz) || C[11]; // rv 1
  assign C_in[12] = (C[12] === 1'bz) || C[12]; // rv 1
  assign C_in[13] = (C[13] === 1'bz) || C[13]; // rv 1
  assign C_in[14] = (C[14] === 1'bz) || C[14]; // rv 1
  assign C_in[15] = (C[15] === 1'bz) || C[15]; // rv 1
  assign C_in[16] = (C[16] === 1'bz) || C[16]; // rv 1
  assign C_in[17] = (C[17] === 1'bz) || C[17]; // rv 1
  assign C_in[18] = (C[18] === 1'bz) || C[18]; // rv 1
  assign C_in[19] = (C[19] === 1'bz) || C[19]; // rv 1
  assign C_in[1] = (C[1] === 1'bz) || C[1]; // rv 1
  assign C_in[20] = (C[20] === 1'bz) || C[20]; // rv 1
  assign C_in[21] = (C[21] === 1'bz) || C[21]; // rv 1
  assign C_in[22] = (C[22] === 1'bz) || C[22]; // rv 1
  assign C_in[23] = (C[23] === 1'bz) || C[23]; // rv 1
  assign C_in[24] = (C[24] === 1'bz) || C[24]; // rv 1
  assign C_in[25] = (C[25] === 1'bz) || C[25]; // rv 1
  assign C_in[26] = (C[26] === 1'bz) || C[26]; // rv 1
  assign C_in[27] = (C[27] === 1'bz) || C[27]; // rv 1
  assign C_in[28] = (C[28] === 1'bz) || C[28]; // rv 1
  assign C_in[29] = (C[29] === 1'bz) || C[29]; // rv 1
  assign C_in[2] = (C[2] === 1'bz) || C[2]; // rv 1
  assign C_in[30] = (C[30] === 1'bz) || C[30]; // rv 1
  assign C_in[31] = (C[31] === 1'bz) || C[31]; // rv 1
  assign C_in[32] = (C[32] === 1'bz) || C[32]; // rv 1
  assign C_in[33] = (C[33] === 1'bz) || C[33]; // rv 1
  assign C_in[34] = (C[34] === 1'bz) || C[34]; // rv 1
  assign C_in[35] = (C[35] === 1'bz) || C[35]; // rv 1
  assign C_in[36] = (C[36] === 1'bz) || C[36]; // rv 1
  assign C_in[37] = (C[37] === 1'bz) || C[37]; // rv 1
  assign C_in[38] = (C[38] === 1'bz) || C[38]; // rv 1
  assign C_in[39] = (C[39] === 1'bz) || C[39]; // rv 1
  assign C_in[3] = (C[3] === 1'bz) || C[3]; // rv 1
  assign C_in[40] = (C[40] === 1'bz) || C[40]; // rv 1
  assign C_in[41] = (C[41] === 1'bz) || C[41]; // rv 1
  assign C_in[42] = (C[42] === 1'bz) || C[42]; // rv 1
  assign C_in[43] = (C[43] === 1'bz) || C[43]; // rv 1
  assign C_in[44] = (C[44] === 1'bz) || C[44]; // rv 1
  assign C_in[45] = (C[45] === 1'bz) || C[45]; // rv 1
  assign C_in[46] = (C[46] === 1'bz) || C[46]; // rv 1
  assign C_in[47] = (C[47] === 1'bz) || C[47]; // rv 1
  assign C_in[4] = (C[4] === 1'bz) || C[4]; // rv 1
  assign C_in[5] = (C[5] === 1'bz) || C[5]; // rv 1
  assign C_in[6] = (C[6] === 1'bz) || C[6]; // rv 1
  assign C_in[7] = (C[7] === 1'bz) || C[7]; // rv 1
  assign C_in[8] = (C[8] === 1'bz) || C[8]; // rv 1
  assign C_in[9] = (C[9] === 1'bz) || C[9]; // rv 1
  assign RSTC_in = (RSTC !== 1'bz) && (RSTC ^ IS_RSTC_INVERTED_REG); // rv 0
`endif

`ifndef XIL_XECLIB
  reg attr_test;
  reg attr_err;

initial begin
  trig_attr = 1'b0;
`ifdef XIL_ATTR_TEST
  attr_test = 1'b1;
`else
  attr_test = 1'b0;
`endif
  attr_err = 1'b0;
  #1;
  trig_attr = ~trig_attr;
end
`endif

`ifdef XIL_XECLIB
  assign CREG_BIN = CREG_REG[0];

`else
always @(trig_attr) begin
#1;
  CREG_BIN = CREG_REG[0];

end
`endif

`ifndef XIL_TIMING
  initial begin
    $display("Error: [Unisim %s-100] SIMPRIM primitive is not intended for direct instantiation in RTL or functional netlists. This primitive is only available in the SIMPRIM library for implemented netlists, please ensure you are pointing to the correct library. Instance %m", MODULE_NAME);
    #1 $finish;
  end
`endif

`ifndef XIL_XECLIB
  always @(trig_attr) begin
  #1;
    if ((attr_test == 1'b1) ||
        ((CREG_REG != 1) &&
         (CREG_REG != 0))) begin
      $display("Error: [Unisim %s-101] CREG attribute is set to %d.  Legal values for this attribute are 1 or 0. Instance: %m", MODULE_NAME, CREG_REG);
      attr_err = 1'b1;
    end

    if (attr_err == 1'b1) #1 $finish;
  end
`endif

`ifdef XIL_TIMING
  reg notifier;
`endif

// begin behavioral model

  localparam C_WIDTH   = 48;
  reg [C_WIDTH-1:0] C_reg;

// initialize regs
`ifndef XIL_XECLIB
initial begin
  C_reg = {C_WIDTH{1'b0}};
end
`endif

//*********************************************************
//*** Input register C with 1 level deep of register
//*********************************************************

   always @(posedge CLK_in) begin
      if (RSTC_in || (CREG_BIN == 1'b0) || glblGSR) begin
         C_reg <= 48'b0;
      end else if (CEC_in) begin
         C_reg <= C_in;
      end
   end

   assign C_DATA     = (CREG_BIN == 1'b1) ? C_reg : C_in;

// end behavioral model

`ifndef XIL_XECLIB
`ifdef XIL_TIMING
  wire clk_en_n;
  wire clk_en_p;

  assign clk_en_n = IS_CLK_INVERTED_REG;
  assign clk_en_p = ~IS_CLK_INVERTED_REG;

`endif
  specify
    (C *> C_DATA) = (0:0:0, 0:0:0);
    (CLK *> C_DATA) = (0:0:0, 0:0:0);
`ifdef XIL_TIMING
    $setuphold (negedge CLK, negedge C, 0:0:0, 0:0:0, notifier, clk_en_n, clk_en_n, CLK_delay, C_delay);
    $setuphold (negedge CLK, negedge CEC, 0:0:0, 0:0:0, notifier, clk_en_n, clk_en_n, CLK_delay, CEC_delay);
    $setuphold (negedge CLK, negedge RSTC, 0:0:0, 0:0:0, notifier, clk_en_n, clk_en_n, CLK_delay, RSTC_delay);
    $setuphold (negedge CLK, posedge C, 0:0:0, 0:0:0, notifier, clk_en_n, clk_en_n, CLK_delay, C_delay);
    $setuphold (negedge CLK, posedge CEC, 0:0:0, 0:0:0, notifier, clk_en_n, clk_en_n, CLK_delay, CEC_delay);
    $setuphold (negedge CLK, posedge RSTC, 0:0:0, 0:0:0, notifier, clk_en_n, clk_en_n, CLK_delay, RSTC_delay);
    $setuphold (posedge CLK, negedge C, 0:0:0, 0:0:0, notifier, clk_en_p, clk_en_p, CLK_delay, C_delay);
    $setuphold (posedge CLK, negedge CEC, 0:0:0, 0:0:0, notifier, clk_en_p, clk_en_p, CLK_delay, CEC_delay);
    $setuphold (posedge CLK, negedge RSTC, 0:0:0, 0:0:0, notifier, clk_en_p, clk_en_p, CLK_delay, RSTC_delay);
    $setuphold (posedge CLK, posedge C, 0:0:0, 0:0:0, notifier, clk_en_p, clk_en_p, CLK_delay, C_delay);
    $setuphold (posedge CLK, posedge CEC, 0:0:0, 0:0:0, notifier, clk_en_p, clk_en_p, CLK_delay, CEC_delay);
    $setuphold (posedge CLK, posedge RSTC, 0:0:0, 0:0:0, notifier, clk_en_p, clk_en_p, CLK_delay, RSTC_delay);
`endif
    specparam PATHPULSE$ = 0;
  endspecify
`endif
endmodule

`endcelldefine
