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
//  /   /                        Clock Buffer
// /___/   /\      Filename    : BUFCE_ROW.v
// \   \  /  \
//  \___\/\___\
//
///////////////////////////////////////////////////////////////////////////////
//  Revision:
//    05/15/12 - Initial version.
//    02/04/14 - update specify block
//    10/22/14 - 808642 - Added #1 to $finish
//  End Revision:
///////////////////////////////////////////////////////////////////////////////

`timescale 1 ps / 1 ps

`celldefine

module BUFCE_ROW #(



  parameter CE_TYPE = "SYNC",
  parameter [0:0] IS_CE_INVERTED = 1'b0,
  parameter [0:0] IS_I_INVERTED = 1'b0
)(
  output O,

  input CE,
  input I
);
  
// define constants
  localparam MODULE_NAME = "BUFCE_ROW";

// Parameter encodings and registers
  localparam CE_TYPE_ASYNC = 1;
  localparam CE_TYPE_HARDSYNC = 2;
  localparam CE_TYPE_SYNC = 0;

  reg trig_attr;
// include dynamic registers - XILINX test only



  reg [64:1] CE_TYPE_REG = CE_TYPE;
  reg [0:0] IS_CE_INVERTED_REG = IS_CE_INVERTED;
  reg [0:0] IS_I_INVERTED_REG = IS_I_INVERTED;





  reg [1:0] CE_TYPE_BIN;





  tri0 glblGSR = glbl.GSR;


  wire CE_in;
  wire I_in;









  assign CE_in = (CE === 1'bz) || (CE ^ IS_CE_INVERTED_REG); // rv 1
  assign I_in = I ^ IS_I_INVERTED_REG;



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
    CE_TYPE_BIN =
      (CE_TYPE_REG == "SYNC") ? CE_TYPE_SYNC :
      (CE_TYPE_REG == "ASYNC") ? CE_TYPE_ASYNC :
      (CE_TYPE_REG == "HARDSYNC") ? CE_TYPE_HARDSYNC :
       CE_TYPE_SYNC;

  end



  initial begin
    $display("Error: [Unisim %s-100] SIMPRIM primitive is not intended for direct instantiation in RTL or functional netlists. This primitive is only available in the SIMPRIM library for implemented netlists, please ensure you are pointing to the correct library. Instance %m", MODULE_NAME);
    #1 $finish;
  end



  always @ (trig_attr) begin
  #1;
    if ((attr_test == 1'b1) ||
        ((CE_TYPE_REG != "SYNC") &&
         (CE_TYPE_REG != "ASYNC") &&
         (CE_TYPE_REG != "HARDSYNC"))) begin
      $display("Error: [Unisim %s-101] CE_TYPE attribute is set to %s.  Legal values for this attribute are SYNC, ASYNC or HARDSYNC. Instance: %m", MODULE_NAME, CE_TYPE_REG);
      attr_err = 1'b1;
    end

    if (attr_err == 1'b1) #1 $finish;
  end






// begin behavioral model

  reg enable_clk = 1'b1;

  always @(I_in or CE_in or glblGSR) begin
  if (glblGSR)
    enable_clk = 1'b1;
  else if ((CE_TYPE_BIN == CE_TYPE_ASYNC) || ~I_in)
    enable_clk = CE_in;
  end

  assign O = enable_clk & I_in;

// end behavioral model




























endmodule

`endcelldefine
