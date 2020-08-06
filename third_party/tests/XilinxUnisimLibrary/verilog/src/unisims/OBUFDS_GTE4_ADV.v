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
//  /   /                        Gigabit Transceiver Buffer
// /___/   /\      Filename    : OBUFDS_GTE4_ADV.v
// \   \  /  \ 
//  \___\/\___\                    
//                                 
///////////////////////////////////////////////////////////////////////////////
//  Revision:
//  03/27/2015 - Initial version from E3
//  End Revision:
///////////////////////////////////////////////////////////////////////////////

`timescale 1 ps / 1 ps 

`celldefine

module OBUFDS_GTE4_ADV #(
`ifdef XIL_TIMING
  parameter LOC = "UNPLACED",  
`endif
  parameter [0:0] REFCLK_EN_TX_PATH = 1'b0,
  parameter [4:0] REFCLK_ICNTL_TX = 5'b00000
)(
  output O,
  output OB,

  input CEB,
  input [3:0] I,
  input [1:0] RXRECCLK_SEL
);
  
// define constants
  localparam MODULE_NAME = "OBUFDS_GTE4_ADV";

  reg trig_attr;
// include dynamic registers - XILINX test only
`ifdef XIL_DR
  `include "OBUFDS_GTE4_ADV_dr.v"
`else
  reg [0:0] REFCLK_EN_TX_PATH_REG = REFCLK_EN_TX_PATH;
  reg [4:0] REFCLK_ICNTL_TX_REG = REFCLK_ICNTL_TX;
`endif

`ifdef XIL_XECLIB
  reg glblGSR = 1'b0;
  reg glblGTS = glbl.GTS;
`else
  tri0 glblGSR = glbl.GSR;
  tri0 glblGTS = glbl.GTS;
`endif

  reg attr_err = 1'b0;
   
//  wire CEB_in;
//  wire [1:0] RXRECCLK_SEL_in;
//  wire [3:0] I_in;

//  assign CEB_in = (CEB !== 1'bz) && CEB; // rv 0
//  assign I_in = I;
//  assign RXRECCLK_SEL_in = RXRECCLK_SEL;

  reg  I_sel = 1'b0;
// =====================
// Generate I_sel
// =====================
  always @(*) begin
    case (RXRECCLK_SEL)
      2'b00: I_sel <= I[0];
      2'b01: I_sel <= I[1];
      2'b10: I_sel <= I[2];
      2'b11: I_sel <= I[3];
      default : I_sel <= I[0];
     endcase
   end

// =====================
// Generate O
// =====================

  assign O = (~REFCLK_EN_TX_PATH_REG || (CEB === 1'b1) || glblGTS) ? 1'bz : I_sel;
  assign OB = (~REFCLK_EN_TX_PATH_REG || (CEB === 1'b1) || glblGTS) ? 1'bz : ~I_sel;

`ifndef XIL_XECLIB
`ifdef XIL_TIMING
  specify
    (CEB => O) = (0:0:0, 0:0:0);
    (CEB => OB) = (0:0:0, 0:0:0);
    (I[0] => O) = (0:0:0, 0:0:0);
    (I[0] => OB) = (0:0:0, 0:0:0);
    (I[1] => O) = (0:0:0, 0:0:0);
    (I[1] => OB) = (0:0:0, 0:0:0);
    (I[2] => O) = (0:0:0, 0:0:0);
    (I[2] => OB) = (0:0:0, 0:0:0);
    (I[3] => O) = (0:0:0, 0:0:0);
    (I[3] => OB) = (0:0:0, 0:0:0);
    specparam PATHPULSE$ = 0;
  endspecify
`endif
`endif
endmodule

`endcelldefine
