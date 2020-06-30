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
//  /   /                        OBUFDS_GTM_ADV
// /___/   /\      Filename    : OBUFDS_GTM_ADV.v
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


module OBUFDS_GTM_ADV #(



  parameter [0:0] REFCLK_EN_TX_PATH = 1'b0,
  parameter integer REFCLK_ICNTL_TX = 0,
  parameter [1:0] RXRECCLK_SEL = 2'b00
)(
  output O,
  output OB,

  input CEB,
  input [3:0] I
);

// define constants
  localparam MODULE_NAME = "OBUFDS_GTM_ADV";
  
  reg trig_attr;
// include dynamic registers - XILINX test only



  reg [0:0] REFCLK_EN_TX_PATH_REG = REFCLK_EN_TX_PATH;
  reg [31:0] REFCLK_ICNTL_TX_REG = REFCLK_ICNTL_TX;
  reg [1:0] RXRECCLK_SEL_REG = RXRECCLK_SEL;





  reg [3:0] REFCLK_ICNTL_TX_BIN;






tri0 glblGSR = glbl.GSR;
tri0 glblGTS = glbl.GTS;



  reg attr_test;
  reg attr_err;
  
  initial begin
  trig_attr = 1'b0;
  


    attr_test = 1'b0;
  
    attr_err = 1'b0;
    #1;
    trig_attr = ~trig_attr;
  end






  always @ (trig_attr) begin
  #1;
  REFCLK_ICNTL_TX_BIN = REFCLK_ICNTL_TX_REG[3:0];
  
  end



  always @ (trig_attr) begin
    #1;
    if ((attr_test == 1'b1) ||
        ((REFCLK_ICNTL_TX_REG != 0) &&
         (REFCLK_ICNTL_TX_REG != 1) &&
         (REFCLK_ICNTL_TX_REG != 3) &&
         (REFCLK_ICNTL_TX_REG != 7) &&
         (REFCLK_ICNTL_TX_REG != 15))) begin
      $display("Error: [Unisim %s-102] REFCLK_ICNTL_TX attribute is set to %d.  Legal values for this attribute are 0, 1, 3, 7 or 15. Instance: %m", MODULE_NAME, REFCLK_ICNTL_TX_REG);
      attr_err = 1'b1;
    end
    
    if (attr_err == 1'b1) #1 $finish;
  end


// begin behavioral model

  reg  I_sel = 1'b0;
// =====================
// Generate I_sel
// =====================
  always @(*) begin
    case (RXRECCLK_SEL_REG)
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





















// end behavioral model

endmodule

`endcelldefine

