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



  reg [0:0] REFCLK_EN_TX_PATH_REG = REFCLK_EN_TX_PATH;
  reg [4:0] REFCLK_ICNTL_TX_REG = REFCLK_ICNTL_TX;






  tri0 glblGSR = glbl.GSR;
  tri0 glblGTS = glbl.GTS;


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


















endmodule

`endcelldefine
