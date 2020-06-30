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
//  /   /                   Static Dual Port Synchronous RAM 32-Deep by 1-Wide
// /___/   /\      Filename    : RAMD32.v
// \   \  /  \
//  \___\/\___\
//
///////////////////////////////////////////////////////////////////////////////
// Revision:
//    07/02/10 - Initial version.
//    12/13/11 - 524859 - Added `celldefine and `endcelldefine.
//    04/16/13 - 683925 - Add invertible pin support.
//    10/22/14 - 808642 - Added #1 to $finish.
// End Revision:
///////////////////////////////////////////////////////////////////////////////

`timescale 1 ps / 1 ps


`celldefine


module RAMD32 #(



  parameter [31:0] INIT = 32'h00000000,
  parameter [0:0] IS_CLK_INVERTED = 1'b0
)(
  output O,

  input CLK,
  input I,
  input RADR0,
  input RADR1,
  input RADR2,
  input RADR3,
  input RADR4,
  input WADR0,
  input WADR1,
  input WADR2,
  input WADR3,
  input WADR4,
  input WE
);
  
// define constants
  localparam MODULE_NAME = "RAMD32";

  reg trig_attr;
// include dynamic registers - XILINX test only



  reg [31:0] INIT_REG = INIT;
  reg [0:0] IS_CLK_INVERTED_REG = IS_CLK_INVERTED;





tri0 glblGSR = glbl.GSR;


  wire CLK_in;
  wire I_in;
  wire RADR0_in;
  wire RADR1_in;
  wire RADR2_in;
  wire RADR3_in;
  wire RADR4_in;
  wire WADR0_in;
  wire WADR1_in;
  wire WADR2_in;
  wire WADR3_in;
  wire WADR4_in;
  wire WE_in;





















  assign CLK_in = CLK ^ IS_CLK_INVERTED_REG;
  assign I_in = I;
  assign WADR0_in = WADR0;
  assign WADR1_in = WADR1;
  assign WADR2_in = WADR2;
  assign WADR3_in = WADR3;
  assign WADR4_in = WADR4;
  assign WE_in = (WE === 1'bz) || WE; // rv 1


  assign RADR0_in = RADR0;
  assign RADR1_in = RADR1;
  assign RADR2_in = RADR2;
  assign RADR3_in = RADR3;
  assign RADR4_in = RADR4;


  initial begin
  trig_attr = 1'b0;
    #1;
    trig_attr = ~trig_attr;
  end



  initial begin
    $display("Error: [Unisim %s-100] SIMPRIM primitive is not intended for direct instantiation in RTL or functional netlists. This primitive is only available in the SIMPRIM library for implemented netlists, please ensure you are pointing to the correct library. Instance %m", MODULE_NAME);
    #1 $finish;
  end






// begin behavioral model

  reg [31:0] mem;
  reg O_out;

  assign O = O_out;


  initial begin
    mem = INIT;
    O_out = mem[{RADR4_in,RADR3_in,RADR2_in,RADR1_in,RADR0_in}];
  end


  always @(posedge CLK_in)
    if (WE_in == 1'b1) begin
      mem[{WADR4_in,WADR3_in,WADR2_in,WADR1_in,WADR0_in}] = I_in;
     end

  always @ (*) begin
    O_out = mem[{RADR4_in,RADR3_in,RADR2_in,RADR1_in,RADR0_in}];
  end





// end behavioral model














  specify
    (CLK => O) = (100:100:100, 100:100:100);
    (I => O) = (0:0:0, 0:0:0);
    (RADR0 => O) = (0:0:0, 0:0:0);
    (RADR1 => O) = (0:0:0, 0:0:0);
    (RADR2 => O) = (0:0:0, 0:0:0);
    (RADR3 => O) = (0:0:0, 0:0:0);
    (RADR4 => O) = (0:0:0, 0:0:0);


































    specparam PATHPULSE$ = 0;
  endspecify

endmodule

`endcelldefine

