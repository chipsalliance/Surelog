///////////////////////////////////////////////////////////////////////////////
//     Copyright (c) 2011 Xilinx Inc.
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
//
//   ____   ___
//  /   /\/   / 
// /___/  \  /     Vendor      : Xilinx 
// \   \   \/      Version     : 2012.2
//  \   \          Description : Xilinx Unified Simulation Library Component
//  /   /                        
// /___/   /\      Filename    : OBUFDS_GTE3_ADV.v
// \   \  /  \ 
//  \___\/\___\                    
//                                 
///////////////////////////////////////////////////////////////////////////////
//  Revision:
//  08/28/2013 - Initial model
//  06/02/14 - New simulation library message format.
//    10/22/14 - Added #1 to $finish (CR 808642).
//  End Revision:
///////////////////////////////////////////////////////////////////////////////

`timescale 1 ps / 1 ps 

`celldefine
module OBUFDS_GTE3_ADV #(
  `ifdef XIL_TIMING //Simprim 
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
  localparam MODULE_NAME = "OBUFDS_GTE3_ADV";

   reg I_delay;

// Parameter encodings and registers

  `ifndef XIL_DR
  localparam [0:0] REFCLK_EN_TX_PATH_REG = REFCLK_EN_TX_PATH;
  localparam [4:0] REFCLK_ICNTL_TX_REG = REFCLK_ICNTL_TX;
  `endif

  wire REFCLK_EN_TX_PATH_BIN;
  wire [4:0] REFCLK_ICNTL_TX_BIN;

   
  tri0 GTS = glbl.GTS;
  tri0 glblGSR = glbl.GSR;

  `ifdef XIL_TIMING //Simprim 
  reg notifier;
  `endif
  
// include dynamic registers - XILINX test only
  `ifdef XIL_DR
  `include "OBUFDS_GTE3_ADV_dr.v"
  `endif

  assign REFCLK_EN_TX_PATH_BIN = REFCLK_EN_TX_PATH_REG;

  assign REFCLK_ICNTL_TX_BIN = REFCLK_ICNTL_TX_REG;

    wire t1;
    wire t2;
   
    or O1 (t1, GTS, CEB);
    or O2 (t2, ~REFCLK_EN_TX_PATH_BIN, t1);


    // =====================
    // Generate I_delay
    // =====================
    always @(*) begin
       case (RXRECCLK_SEL)
	 2'b00: I_delay <= I[0];
         2'b01: I_delay <= I[1];
         2'b10: I_delay <= I[2];
         2'b11: I_delay <= I[3];
         default : I_delay <= I[0];
	   endcase
    end

    bufif0 B1 (O, I_delay, t2);
    notif0 N1 (OB, I_delay, t2);
      

    specify
    (I[0] => O) = (0:0:0, 0:0:0);
    (I[0] => OB) = (0:0:0, 0:0:0);
    (I[1] => O) = (0:0:0, 0:0:0);
    (I[1] => OB) = (0:0:0, 0:0:0);
    (I[2] => O) = (0:0:0, 0:0:0);
    (I[2] => OB) = (0:0:0, 0:0:0);
    (I[3] => O) = (0:0:0, 0:0:0);
    (I[3] => OB) = (0:0:0, 0:0:0);
    (CEB => O) = (0:0:0, 0:0:0);
    (CEB => OB) = (0:0:0, 0:0:0);
    specparam PATHPULSE$ = 0;
  endspecify

  
  endmodule

`endcelldefine
