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
// \   \   \/      Version     : 2016.4
//  \   \          Description : Xilinx Unified Simulation Library Component
//  /   /                        Fast Carry Logic with Look Ahead
// /___/   /\      Filename    : CARRY8.v
// \   \  /  \
//  \___\/\___\
//
///////////////////////////////////////////////////////////////////////////////
//  Revision
//    09/26/12 - Initial functional version.
//    05/24/13 - Add CARRY_TYPE, CI_TOP
//    10/22/14 - 808642 - Added #1 to $finish
//  End Revision
///////////////////////////////////////////////////////////////////////////////

`timescale 1 ps / 1 ps

`celldefine

module CARRY8 #(
`ifdef XIL_TIMING
  parameter LOC = "UNPLACED",
`endif
  parameter CARRY_TYPE = "SINGLE_CY8"
)(
  output [7:0] CO,
  output [7:0] O,

  input CI,
  input CI_TOP,
  input [7:0] DI,
  input [7:0] S
);
  
// define constants
  localparam MODULE_NAME = "CARRY8";

// Parameter encodings and registers
  localparam CARRY_TYPE_DUAL_CY4 = 1;
  localparam CARRY_TYPE_SINGLE_CY8 = 0;

  reg trig_attr = 1'b0;
// include dynamic registers - XILINX test only
`ifdef XIL_DR
  `include "CARRY8_dr.v"
`else
  reg [80:1] CARRY_TYPE_REG = CARRY_TYPE;
`endif

`ifdef XIL_XECLIB
  wire CARRY_TYPE_BIN;
`else
  reg CARRY_TYPE_BIN;
`endif

`ifdef XIL_ATTR_TEST
  reg attr_test = 1'b1;
`else
  reg attr_test = 1'b0;
`endif
  reg attr_err = 1'b0;

  wire CI_TOP_in;
  wire CI_in;
  wire [7:0] DI_in;
  wire [7:0] S_in;


  assign CI_TOP_in = ((CI_TOP !== 1'bz) &&
                      ((CARRY_TYPE_BIN == CARRY_TYPE_DUAL_CY4) && CI_TOP)) ||
                     ((CARRY_TYPE_BIN == CARRY_TYPE_SINGLE_CY8) && CO[3]); // rv 0
  assign CI_in = (CI !== 1'bz) && CI; // rv 0
  assign DI_in[7] = (DI[7] !== 1'bz) && DI[7]; // rv 0
  assign DI_in[6] = (DI[6] !== 1'bz) && DI[6]; // rv 0
  assign DI_in[5] = (DI[5] !== 1'bz) && DI[5]; // rv 0
  assign DI_in[4] = (DI[4] !== 1'bz) && DI[4]; // rv 0
  assign DI_in[3] = (DI[3] !== 1'bz) && DI[3]; // rv 0
  assign DI_in[2] = (DI[2] !== 1'bz) && DI[2]; // rv 0
  assign DI_in[1] = (DI[1] !== 1'bz) && DI[1]; // rv 0
  assign DI_in[0] = (DI[0] !== 1'bz) && DI[0]; // rv 0
  assign S_in[7] = (S[7] !== 1'bz) && S[7]; // rv 0
  assign S_in[6] = (S[6] !== 1'bz) && S[6]; // rv 0
  assign S_in[5] = (S[5] !== 1'bz) && S[5]; // rv 0
  assign S_in[4] = (S[4] !== 1'bz) && S[4]; // rv 0
  assign S_in[3] = (S[3] !== 1'bz) && S[3]; // rv 0
  assign S_in[2] = (S[2] !== 1'bz) && S[2]; // rv 0
  assign S_in[1] = (S[1] !== 1'bz) && S[1]; // rv 0
  assign S_in[0] = (S[0] !== 1'bz) && S[0]; // rv 0

`ifndef XIL_XECLIB
  initial begin
    #1;
    trig_attr = ~trig_attr;
  end
`endif

`ifdef XIL_XECLIB
  assign CARRY_TYPE_BIN =
    (CARRY_TYPE_REG == "SINGLE_CY8") ? CARRY_TYPE_SINGLE_CY8 :
    (CARRY_TYPE_REG == "DUAL_CY4") ? CARRY_TYPE_DUAL_CY4 :
     CARRY_TYPE_SINGLE_CY8;

`else
  always @(trig_attr) begin
  #1;
  CARRY_TYPE_BIN =
    (CARRY_TYPE_REG == "SINGLE_CY8") ? CARRY_TYPE_SINGLE_CY8 :
    (CARRY_TYPE_REG == "DUAL_CY4") ? CARRY_TYPE_DUAL_CY4 :
     CARRY_TYPE_SINGLE_CY8;

  end
`endif

`ifndef XIL_XECLIB
always @ (trig_attr) begin
  #1;
    if ((attr_test == 1'b1) ||
        ((CARRY_TYPE_REG != "SINGLE_CY8") &&
         (CARRY_TYPE_REG != "DUAL_CY4"))) begin
      $display("Error: [Unisim %s-101] CARRY_TYPE attribute is set to %s.  Legal values for this attribute are SINGLE_CY8 or DUAL_CY4. Instance: %m", MODULE_NAME, CARRY_TYPE_REG);
      attr_err = 1'b1;
    end

    if (attr_err == 1'b1) #1 $finish;
  end
`endif

  wire [7:0] CO_fb;
  assign CO_fb = {CO[6:4], CI_TOP_in, CO[2:0], CI_in};
  assign O = S_in ^ CO_fb;
  assign CO = (S_in & CO_fb) | (~S_in & DI_in);

`ifndef XIL_XECLIB
`ifdef XIL_TIMING
  specify
    (CI => CO[0]) = (0:0:0, 0:0:0);
    (CI => CO[1]) = (0:0:0, 0:0:0);
    (CI => CO[2]) = (0:0:0, 0:0:0);
    (CI => CO[3]) = (0:0:0, 0:0:0);
    (CI => CO[4]) = (0:0:0, 0:0:0);
    (CI => CO[5]) = (0:0:0, 0:0:0);
    (CI => CO[6]) = (0:0:0, 0:0:0);
    (CI => CO[7]) = (0:0:0, 0:0:0);
    (CI => O[0]) = (0:0:0, 0:0:0);
    (CI => O[1]) = (0:0:0, 0:0:0);
    (CI => O[2]) = (0:0:0, 0:0:0);
    (CI => O[3]) = (0:0:0, 0:0:0);
    (CI => O[4]) = (0:0:0, 0:0:0);
    (CI => O[5]) = (0:0:0, 0:0:0);
    (CI => O[6]) = (0:0:0, 0:0:0);
    (CI => O[7]) = (0:0:0, 0:0:0);
    (CI_TOP => CO[4]) = (0:0:0, 0:0:0);
    (CI_TOP => CO[5]) = (0:0:0, 0:0:0);
    (CI_TOP => CO[6]) = (0:0:0, 0:0:0);
    (CI_TOP => CO[7]) = (0:0:0, 0:0:0);
    (CI_TOP => O[4]) = (0:0:0, 0:0:0);
    (CI_TOP => O[5]) = (0:0:0, 0:0:0);
    (CI_TOP => O[6]) = (0:0:0, 0:0:0);
    (CI_TOP => O[7]) = (0:0:0, 0:0:0);
    (DI[0] => CO[0]) = (0:0:0, 0:0:0);
    (DI[0] => CO[1]) = (0:0:0, 0:0:0);
    (DI[0] => CO[2]) = (0:0:0, 0:0:0);
    (DI[0] => CO[3]) = (0:0:0, 0:0:0);
    (DI[0] => CO[4]) = (0:0:0, 0:0:0);
    (DI[0] => CO[5]) = (0:0:0, 0:0:0);
    (DI[0] => CO[6]) = (0:0:0, 0:0:0);
    (DI[0] => CO[7]) = (0:0:0, 0:0:0);
    (DI[0] => O[0]) = (0:0:0, 0:0:0);
    (DI[0] => O[1]) = (0:0:0, 0:0:0);
    (DI[0] => O[2]) = (0:0:0, 0:0:0);
    (DI[0] => O[3]) = (0:0:0, 0:0:0);
    (DI[0] => O[4]) = (0:0:0, 0:0:0);
    (DI[0] => O[5]) = (0:0:0, 0:0:0);
    (DI[0] => O[6]) = (0:0:0, 0:0:0);
    (DI[0] => O[7]) = (0:0:0, 0:0:0);
    (DI[1] => CO[1]) = (0:0:0, 0:0:0);
    (DI[1] => CO[2]) = (0:0:0, 0:0:0);
    (DI[1] => CO[3]) = (0:0:0, 0:0:0);
    (DI[1] => CO[4]) = (0:0:0, 0:0:0);
    (DI[1] => CO[5]) = (0:0:0, 0:0:0);
    (DI[1] => CO[6]) = (0:0:0, 0:0:0);
    (DI[1] => CO[7]) = (0:0:0, 0:0:0);
    (DI[1] => O[2]) = (0:0:0, 0:0:0);
    (DI[1] => O[3]) = (0:0:0, 0:0:0);
    (DI[1] => O[4]) = (0:0:0, 0:0:0);
    (DI[1] => O[5]) = (0:0:0, 0:0:0);
    (DI[1] => O[6]) = (0:0:0, 0:0:0);
    (DI[1] => O[7]) = (0:0:0, 0:0:0);
    (DI[2] => CO[2]) = (0:0:0, 0:0:0);
    (DI[2] => CO[3]) = (0:0:0, 0:0:0);
    (DI[2] => CO[4]) = (0:0:0, 0:0:0);
    (DI[2] => CO[5]) = (0:0:0, 0:0:0);
    (DI[2] => CO[6]) = (0:0:0, 0:0:0);
    (DI[2] => CO[7]) = (0:0:0, 0:0:0);
    (DI[2] => O[3]) = (0:0:0, 0:0:0);
    (DI[2] => O[4]) = (0:0:0, 0:0:0);
    (DI[2] => O[5]) = (0:0:0, 0:0:0);
    (DI[2] => O[6]) = (0:0:0, 0:0:0);
    (DI[2] => O[7]) = (0:0:0, 0:0:0);
    (DI[3] => CO[3]) = (0:0:0, 0:0:0);
    (DI[3] => CO[4]) = (0:0:0, 0:0:0);
    (DI[3] => CO[5]) = (0:0:0, 0:0:0);
    (DI[3] => CO[6]) = (0:0:0, 0:0:0);
    (DI[3] => CO[7]) = (0:0:0, 0:0:0);
    (DI[3] => O[4]) = (0:0:0, 0:0:0);
    (DI[3] => O[5]) = (0:0:0, 0:0:0);
    (DI[3] => O[6]) = (0:0:0, 0:0:0);
    (DI[3] => O[7]) = (0:0:0, 0:0:0);
    (DI[4] => CO[4]) = (0:0:0, 0:0:0);
    (DI[4] => CO[5]) = (0:0:0, 0:0:0);
    (DI[4] => CO[6]) = (0:0:0, 0:0:0);
    (DI[4] => CO[7]) = (0:0:0, 0:0:0);
    (DI[4] => O[5]) = (0:0:0, 0:0:0);
    (DI[4] => O[6]) = (0:0:0, 0:0:0);
    (DI[4] => O[7]) = (0:0:0, 0:0:0);
    (DI[5] => CO[5]) = (0:0:0, 0:0:0);
    (DI[5] => CO[6]) = (0:0:0, 0:0:0);
    (DI[5] => CO[7]) = (0:0:0, 0:0:0);
    (DI[5] => O[6]) = (0:0:0, 0:0:0);
    (DI[5] => O[7]) = (0:0:0, 0:0:0);
    (DI[6] => CO[6]) = (0:0:0, 0:0:0);
    (DI[6] => CO[7]) = (0:0:0, 0:0:0);
    (DI[6] => O[7]) = (0:0:0, 0:0:0);
    (DI[7] => CO[7]) = (0:0:0, 0:0:0);
    (S[0] => CO[0]) = (0:0:0, 0:0:0);
    (S[0] => CO[1]) = (0:0:0, 0:0:0);
    (S[0] => CO[2]) = (0:0:0, 0:0:0);
    (S[0] => CO[3]) = (0:0:0, 0:0:0);
    (S[0] => CO[4]) = (0:0:0, 0:0:0);
    (S[0] => CO[5]) = (0:0:0, 0:0:0);
    (S[0] => CO[6]) = (0:0:0, 0:0:0);
    (S[0] => CO[7]) = (0:0:0, 0:0:0);
    (S[0] => O[0]) = (0:0:0, 0:0:0);
    (S[0] => O[1]) = (0:0:0, 0:0:0);
    (S[0] => O[2]) = (0:0:0, 0:0:0);
    (S[0] => O[3]) = (0:0:0, 0:0:0);
    (S[0] => O[4]) = (0:0:0, 0:0:0);
    (S[0] => O[5]) = (0:0:0, 0:0:0);
    (S[0] => O[6]) = (0:0:0, 0:0:0);
    (S[0] => O[7]) = (0:0:0, 0:0:0);
    (S[1] => CO[1]) = (0:0:0, 0:0:0);
    (S[1] => CO[2]) = (0:0:0, 0:0:0);
    (S[1] => CO[3]) = (0:0:0, 0:0:0);
    (S[1] => CO[4]) = (0:0:0, 0:0:0);
    (S[1] => CO[5]) = (0:0:0, 0:0:0);
    (S[1] => CO[6]) = (0:0:0, 0:0:0);
    (S[1] => CO[7]) = (0:0:0, 0:0:0);
    (S[1] => O[1]) = (0:0:0, 0:0:0);
    (S[1] => O[2]) = (0:0:0, 0:0:0);
    (S[1] => O[3]) = (0:0:0, 0:0:0);
    (S[1] => O[4]) = (0:0:0, 0:0:0);
    (S[1] => O[5]) = (0:0:0, 0:0:0);
    (S[1] => O[6]) = (0:0:0, 0:0:0);
    (S[1] => O[7]) = (0:0:0, 0:0:0);
    (S[2] => CO[2]) = (0:0:0, 0:0:0);
    (S[2] => CO[3]) = (0:0:0, 0:0:0);
    (S[2] => CO[4]) = (0:0:0, 0:0:0);
    (S[2] => CO[5]) = (0:0:0, 0:0:0);
    (S[2] => CO[6]) = (0:0:0, 0:0:0);
    (S[2] => CO[7]) = (0:0:0, 0:0:0);
    (S[2] => O[2]) = (0:0:0, 0:0:0);
    (S[2] => O[3]) = (0:0:0, 0:0:0);
    (S[2] => O[4]) = (0:0:0, 0:0:0);
    (S[2] => O[5]) = (0:0:0, 0:0:0);
    (S[2] => O[6]) = (0:0:0, 0:0:0);
    (S[2] => O[7]) = (0:0:0, 0:0:0);
    (S[3] => CO[3]) = (0:0:0, 0:0:0);
    (S[3] => CO[4]) = (0:0:0, 0:0:0);
    (S[3] => CO[5]) = (0:0:0, 0:0:0);
    (S[3] => CO[6]) = (0:0:0, 0:0:0);
    (S[3] => CO[7]) = (0:0:0, 0:0:0);
    (S[3] => O[3]) = (0:0:0, 0:0:0);
    (S[3] => O[4]) = (0:0:0, 0:0:0);
    (S[3] => O[5]) = (0:0:0, 0:0:0);
    (S[3] => O[6]) = (0:0:0, 0:0:0);
    (S[3] => O[7]) = (0:0:0, 0:0:0);
    (S[4] => CO[4]) = (0:0:0, 0:0:0);
    (S[4] => CO[5]) = (0:0:0, 0:0:0);
    (S[4] => CO[6]) = (0:0:0, 0:0:0);
    (S[4] => CO[7]) = (0:0:0, 0:0:0);
    (S[4] => O[4]) = (0:0:0, 0:0:0);
    (S[4] => O[5]) = (0:0:0, 0:0:0);
    (S[4] => O[6]) = (0:0:0, 0:0:0);
    (S[4] => O[7]) = (0:0:0, 0:0:0);
    (S[5] => CO[5]) = (0:0:0, 0:0:0);
    (S[5] => CO[6]) = (0:0:0, 0:0:0);
    (S[5] => CO[7]) = (0:0:0, 0:0:0);
    (S[5] => O[5]) = (0:0:0, 0:0:0);
    (S[5] => O[6]) = (0:0:0, 0:0:0);
    (S[5] => O[7]) = (0:0:0, 0:0:0);
    (S[6] => CO[6]) = (0:0:0, 0:0:0);
    (S[6] => CO[7]) = (0:0:0, 0:0:0);
    (S[6] => O[6]) = (0:0:0, 0:0:0);
    (S[6] => O[7]) = (0:0:0, 0:0:0);
    (S[7] => CO[7]) = (0:0:0, 0:0:0);
    (S[7] => O[7]) = (0:0:0, 0:0:0);
    specparam PATHPULSE$ = 0;
  endspecify
`endif
`endif

endmodule

`endcelldefine
