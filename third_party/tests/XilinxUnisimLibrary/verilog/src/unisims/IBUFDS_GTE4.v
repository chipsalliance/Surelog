///////////////////////////////////////////////////////////////////////////////
//     Copyright (c) 1995/2017 Xilinx, Inc.
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
//  \   \          Description : Xilinx Unified Simulation Library Component
//  /   /                        Gigabit Transceiver Buffer
// /___/   /\      Filename    : IBUFDS_GTE4.v
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

module IBUFDS_GTE4 #(
`ifdef XIL_TIMING
  parameter LOC = "UNPLACED",  
`endif
  parameter [0:0] REFCLK_EN_TX_PATH = 1'b0,
  parameter [1:0] REFCLK_HROW_CK_SEL = 2'b00,
  parameter [1:0] REFCLK_ICNTL_RX = 2'b00
)(
  output O,
  output ODIV2,

  input CEB,
  input I,
  input IB
);
  
// define constants
  localparam MODULE_NAME = "IBUFDS_GTE4";

  reg trig_attr = 1'b0;
// include dynamic registers - XILINX test only
`ifdef XIL_DR
  `include "IBUFDS_GTE4_dr.v"
`else
  reg [0:0] REFCLK_EN_TX_PATH_REG = REFCLK_EN_TX_PATH;
  reg [1:0] REFCLK_HROW_CK_SEL_REG = REFCLK_HROW_CK_SEL;
  reg [1:0] REFCLK_ICNTL_RX_REG = REFCLK_ICNTL_RX;
`endif

`ifdef XIL_ATTR_TEST
  reg attr_test = 1'b1;
`else
  reg attr_test = 1'b0;
`endif

  reg attr_err = 1'b0;
  tri0 glblGSR = glbl.GSR;
   
//  wire CEB_in;
//  wire IB_in;
//  wire I_in;

//  assign CEB_in = (CEB !== 1'bz) && CEB; // rv 0
//  assign IB_in = IB;
//  assign I_in = I;

  reg  ODIV2_out = 1'b0;
  assign ODIV2   = ODIV2_out;

  reg [2:0] ce_count = 3'b001;
  reg [2:0] edge_count = 3'b000;

  reg allEqual = 1'b0;

// =====================
// Count the rising edges of the clk
// =====================
  always @(posedge I) begin
    if (allEqual)
      edge_count <= 3'b000;
    else
      if ((CEB === 1'b0) || (CEB === 1'bz)) // rv = 0
        edge_count <= edge_count + 1;
    end

//  Generate synchronous reset after DIVIDE number of counts
  always @(edge_count)
    if (edge_count == ce_count)
      allEqual = 1;
    else
      allEqual = 0;

// =====================
// Generate ODIV2
// =====================
  always @(*) begin
    case (REFCLK_HROW_CK_SEL_REG)
      2'b00:    ODIV2_out <= ~(REFCLK_EN_TX_PATH_REG | (CEB === 1'b1)) && I;
      2'b01:    ODIV2_out <= allEqual;
      2'b10:    ODIV2_out <= 1'b0;
      2'b11:    ODIV2_out <= 1'b0;
      default : ODIV2_out <= ~(REFCLK_EN_TX_PATH_REG | (CEB === 1'b1)) && I;
    endcase
  end

// =====================
// Generate O
// =====================

  assign O = ~(REFCLK_EN_TX_PATH_REG | (CEB === 1'b1)) && I;

`ifndef XIL_XECLIB
//`ifdef XIL_TIMING
// "I" is actually a CLK so need I -> O/ODIV2 delays in functional as well.

// IB to O/ODIV2 delay added because this was creating confusion in some tools 
// even though IB input behavior is not modeled. 
  specify
    (I => O) = (100:100:100, 100:100:100);
    (I => ODIV2) = (100:100:100, 100:100:100);
    (IB => O) = (100:100:100, 100:100:100);
    (IB => ODIV2) = (100:100:100, 100:100:100);
    specparam PATHPULSE$ = 0;
  endspecify
//`endif
`endif
endmodule

`endcelldefine
