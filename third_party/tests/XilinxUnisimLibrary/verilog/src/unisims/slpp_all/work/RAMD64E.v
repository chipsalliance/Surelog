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
//  /   /                   Static Dual Port Synchronous RAM 64-Deep by 1-Wide
// /___/   /\      Filename    : RAMD64E.v
// \   \  /  \
//  \___\/\___\
//
///////////////////////////////////////////////////////////////////////////////
// Revision:
//    07/02/10 - Initial version.
//    12/13/11 - 524859 - Added `celldefine and `endcelldefine.
//    03/21/12 - 649330 - Add RAM_ADDRESS_MASK to allow floating WADR6/7.
//    04/16/13 - 683925 - Add invertible pin support.
//    10/22/14 - 808642 - Added #1 to $finish.
// End Revision:
///////////////////////////////////////////////////////////////////////////////

`timescale 1 ps / 1 ps

`celldefine

module RAMD64E #(



  parameter [63:0] INIT = 64'h0000000000000000,
  parameter [0:0] IS_CLK_INVERTED = 1'b0,
  parameter [1:0] RAM_ADDRESS_MASK = 2'b00,
  parameter [1:0] RAM_ADDRESS_SPACE = 2'b00
)(
  output O,

  input CLK,
  input I,
  input RADR0,
  input RADR1,
  input RADR2,
  input RADR3,
  input RADR4,
  input RADR5,
  input WADR0,
  input WADR1,
  input WADR2,
  input WADR3,
  input WADR4,
  input WADR5,
  input WADR6,
  input WADR7,
  input WE
);
  
// define constants
  localparam MODULE_NAME = "RAMD64E";

  reg trig_attr = 1'b0;
// include dynamic registers - XILINX test only



  reg [63:0] INIT_REG = INIT;
  reg [0:0] IS_CLK_INVERTED_REG = IS_CLK_INVERTED;
  reg [1:0] RAM_ADDRESS_MASK_REG = RAM_ADDRESS_MASK;
  reg [1:0] RAM_ADDRESS_SPACE_REG = RAM_ADDRESS_SPACE;





  reg IS_CLK_INVERTED_BIN;





  reg attr_test = 1'b0;

  reg attr_err = 1'b0;

  wire CLK_in;
  wire I_in;
  wire RADR0_in;
  wire RADR1_in;
  wire RADR2_in;
  wire RADR3_in;
  wire RADR4_in;
  wire RADR5_in;
  wire WADR0_in;
  wire WADR1_in;
  wire WADR2_in;
  wire WADR3_in;
  wire WADR4_in;
  wire WADR5_in;
  wire WADR6_in;
  wire WADR7_in;
  wire WE_in;



























  assign CLK_in = CLK ^ IS_CLK_INVERTED_BIN;
  assign I_in = I;
  assign WADR0_in = WADR0;
  assign WADR1_in = WADR1;
  assign WADR2_in = WADR2;
  assign WADR3_in = WADR3;
  assign WADR4_in = WADR4;
  assign WADR5_in = WADR5;
  assign WADR6_in = WADR6;
  assign WADR7_in = WADR7;
  assign WE_in = (WE === 1'bz) || WE; // rv 1

  assign RADR0_in = RADR0;
  assign RADR1_in = RADR1;
  assign RADR2_in = RADR2;
  assign RADR3_in = RADR3;
  assign RADR4_in = RADR4;
  assign RADR5_in = RADR5;


  initial begin
    #1;
    trig_attr = ~trig_attr;
  end






  always @ (trig_attr) begin
  #1;
  IS_CLK_INVERTED_BIN = IS_CLK_INVERTED_REG;

  end



  initial begin
    $display("Error: [Unisim %s-101] SIMPRIM primitive is not intended for direct instantiation in RTL or functional netlists. This primitive is only available in the SIMPRIM library for implemented netlists, please ensure you are pointing to the correct library. Instance %m", MODULE_NAME);
    #1 $finish;
  end






// begin behavioral model

  reg [63:0] mem;
  reg O_out;

  assign O = O_out;


  initial begin
    mem = INIT;
    O_out = mem[{RADR5_in,RADR4_in,RADR3_in,RADR2_in,RADR1_in,RADR0_in}];
  end


  always @(posedge CLK_in)
    if (WE_in == 1'b1 &&
        (RAM_ADDRESS_MASK_REG[1] || WADR7_in == RAM_ADDRESS_SPACE_REG[1]) &&
        (RAM_ADDRESS_MASK_REG[0] || WADR6_in == RAM_ADDRESS_SPACE_REG[0]) ) begin
      mem[{WADR5_in,WADR4_in,WADR3_in,WADR2_in,WADR1_in,WADR0_in}] = I_in;
     end

  always @ (*) begin
    O_out = mem[{RADR5_in,RADR4_in,RADR3_in,RADR2_in,RADR1_in,RADR0_in}];
  end





// end behavioral model

















  specify
    (CLK => O) = (100:100:100, 100:100:100);
    (RADR0 => O) = (0:0:0, 0:0:0);
    (RADR1 => O) = (0:0:0, 0:0:0);
    (RADR2 => O) = (0:0:0, 0:0:0);
    (RADR3 => O) = (0:0:0, 0:0:0);
    (RADR4 => O) = (0:0:0, 0:0:0);
    (RADR5 => O) = (0:0:0, 0:0:0);














































    specparam PATHPULSE$ = 0;
  endspecify


endmodule

`endcelldefine
