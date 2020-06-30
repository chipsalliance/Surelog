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
//  /   /                   Static Single Port Synchronous RAM 32-Deep by 1-Wide
// /___/   /\      Filename    : RAMS32.v
// \   \  /  \
//  \___\/\___\
//
///////////////////////////////////////////////////////////////////////////////
// Revision:
//    07/02/10 - Initial version.
//    12/13/11 - 524859 - Added `celldefine and `endcelldefine.
//    04/16/13 - 683925 - add invertible pin support.
//    10/22/14 - 808642 - Added #1 to $finish.
// End Revision:
///////////////////////////////////////////////////////////////////////////////

`timescale 1 ps / 1 ps


`celldefine


module RAMS32 #(



  parameter [31:0] INIT = 32'h00000000,
  parameter [0:0] IS_CLK_INVERTED = 1'b0
)(
  output O,

  input ADR0,
  input ADR1,
  input ADR2,
  input ADR3,
  input ADR4,
  input CLK,
  input I,
  input WE
);
  
// define constants
  localparam MODULE_NAME = "RAMS32";

  reg trig_attr;
// include dynamic registers - XILINX test only



  reg [31:0] INIT_REG = INIT;
  reg [0:0] IS_CLK_INVERTED_REG = IS_CLK_INVERTED;





tri0 glblGSR = glbl.GSR;


  wire ADR0_in;
  wire ADR1_in;
  wire ADR2_in;
  wire ADR3_in;
  wire ADR4_in;
  wire CLK_in;
  wire I_in;
  wire WE_in;





















  assign ADR0_in = ADR0;
  assign ADR1_in = ADR1;
  assign ADR2_in = ADR2;
  assign ADR3_in = ADR3;
  assign ADR4_in = ADR4;
  assign CLK_in = CLK ^ IS_CLK_INVERTED_REG;
  assign I_in = I;
  assign WE_in = (WE === 1'bz) || WE; // rv 1



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
    O_out = mem[{ADR4_in, ADR3_in, ADR2_in, ADR1_in, ADR0_in}];
  end


  always @(posedge CLK_in)
    if (WE_in == 1'b1) begin
      mem[{ADR4_in, ADR3_in, ADR2_in, ADR1_in, ADR0_in}] = I_in;
    end

  always @ (*) begin
    O_out = mem[{ADR4_in, ADR3_in, ADR2_in, ADR1_in, ADR0_in}];
  end





// end behavioral model

















  specify
    (ADR0 => O) = (0:0:0, 0:0:0);
    (ADR1 => O) = (0:0:0, 0:0:0);
    (ADR2 => O) = (0:0:0, 0:0:0);
    (ADR3 => O) = (0:0:0, 0:0:0);
    (ADR4 => O) = (0:0:0, 0:0:0);
    (CLK => O) = (100:100:100, 100:100:100);
    (I => O) = (0:0:0, 0:0:0);


































    specparam PATHPULSE$ = 0;
  endspecify


endmodule

`endcelldefine

