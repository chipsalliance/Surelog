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
//  /   /                   Static Single Port Synchronous RAM 64-Deep by 1-Wide
// /___/   /\      Filename    : RAMS64E1.v
// \   \  /  \
//  \___\/\___\
//
///////////////////////////////////////////////////////////////////////////////
// Revision:
//    04/16/13 - Initial from RAMS64E.
//    10/22/14 - 808642 - Added #1 to $finish.
// End Revision:
///////////////////////////////////////////////////////////////////////////////

`timescale 1 ps / 1 ps

`celldefine

module RAMS64E1 #(



  parameter [63:0] INIT = 64'h0000000000000000,
  parameter [0:0] IS_CLK_INVERTED = 1'b0,
  parameter [2:0] RAM_ADDRESS_MASK = 3'b000,
  parameter [2:0] RAM_ADDRESS_SPACE = 3'b000
)(
  output O,

  input ADR0,
  input ADR1,
  input ADR2,
  input ADR3,
  input ADR4,
  input ADR5,
  input CLK,
  input I,
  input WADR6,
  input WADR7,
  input WADR8,
  input WE
);
  
// define constants
  localparam MODULE_NAME = "RAMS64E1";

  reg trig_attr = 1'b0;
// include dynamic registers - XILINX test only



  reg [63:0] INIT_REG = INIT;
  reg [0:0] IS_CLK_INVERTED_REG = IS_CLK_INVERTED;
  reg [2:0] RAM_ADDRESS_MASK_REG = RAM_ADDRESS_MASK;
  reg [2:0] RAM_ADDRESS_SPACE_REG = RAM_ADDRESS_SPACE;





  reg IS_CLK_INVERTED_BIN;





  reg attr_test = 1'b0;

  reg attr_err = 1'b0;

  wire ADR0_in;
  wire ADR1_in;
  wire ADR2_in;
  wire ADR3_in;
  wire ADR4_in;
  wire ADR5_in;
  wire CLK_in;
  wire I_in;
  wire WADR6_in;
  wire WADR7_in;
  wire WADR8_in;
  wire WE_in;





























  assign ADR0_in = ADR0;
  assign ADR1_in = ADR1;
  assign ADR2_in = ADR2;
  assign ADR3_in = ADR3;
  assign ADR4_in = ADR4;
  assign ADR5_in = ADR5;
  assign CLK_in = CLK ^ IS_CLK_INVERTED_BIN;
  assign I_in = I;
  assign WADR6_in = WADR6;
  assign WADR7_in = WADR7;
  assign WADR8_in = WADR8;
  assign WE_in = (WE === 1'bz) || WE; // rv 1



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
    O_out = mem[{ADR5_in, ADR4_in, ADR3_in, ADR2_in, ADR1_in, ADR0_in}];
  end


  always @(posedge CLK_in)
    if (WE_in == 1'b1 &&
        (RAM_ADDRESS_MASK_REG[2] || WADR8_in == RAM_ADDRESS_SPACE_REG[2]) &&
        (RAM_ADDRESS_MASK_REG[1] || WADR7_in == RAM_ADDRESS_SPACE_REG[1]) &&
        (RAM_ADDRESS_MASK_REG[0] || WADR6_in == RAM_ADDRESS_SPACE_REG[0]) ) begin
      mem[{ADR5_in, ADR4_in, ADR3_in, ADR2_in, ADR1_in, ADR0_in}] = I_in;
    end

   always @ (*) begin
     O_out = mem[{ADR5_in, ADR4_in, ADR3_in, ADR2_in, ADR1_in, ADR0_in}];
   end





// end behavioral model


  wire clk_en_n;
  wire clk_en_p;
  wire we_clk_en_n;
  wire we_clk_en_p;

  assign clk_en_n = IS_CLK_INVERTED_BIN;
  assign clk_en_p = ~IS_CLK_INVERTED_BIN;
  assign we_clk_en_n = WE_in && IS_CLK_INVERTED_BIN;
  assign we_clk_en_p = WE_in && ~IS_CLK_INVERTED_BIN;

  specify
    (ADR0 => O) = (0:0:0, 0:0:0);
    (ADR1 => O) = (0:0:0, 0:0:0);
    (ADR2 => O) = (0:0:0, 0:0:0);
    (ADR3 => O) = (0:0:0, 0:0:0);
    (ADR4 => O) = (0:0:0, 0:0:0);
    (ADR5 => O) = (0:0:0, 0:0:0);
    (CLK => O) = (100:100:100, 100:100:100);


















































    specparam PATHPULSE$ = 0;
  endspecify


endmodule

`endcelldefine
