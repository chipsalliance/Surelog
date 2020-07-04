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
//  /   /                        DSP_M_DATA
// /___/   /\      Filename    : DSP_M_DATA.v
// \   \  /  \
//  \___\/\___\
//
///////////////////////////////////////////////////////////////////////////////
//  Revision:
//  07/15/12 - Migrate from E1.
//  12/10/12 - Add dynamic registers
//  04/22/13 - 713695 - Zero mult result on USE_SIMD
//  04/23/13 - 714772 - remove sensitivity to negedge GSR
//  10/22/14 - 808642 - Added #1 to $finish
//  End Revision:
///////////////////////////////////////////////////////////////////////////////

`timescale 1 ps / 1 ps

`celldefine

module DSP_M_DATA #(



  parameter [0:0] IS_CLK_INVERTED = 1'b0,
  parameter [0:0] IS_RSTM_INVERTED = 1'b0,
  parameter integer MREG = 1
)(
  output [44:0] U_DATA,
  output [44:0] V_DATA,

  input CEM,
  input CLK,
  input RSTM,
  input [44:0] U,
  input [44:0] V
);
  
// define constants
  localparam MODULE_NAME = "DSP_M_DATA";

  reg trig_attr;
// include dynamic registers - XILINX test only



  reg [0:0] IS_CLK_INVERTED_REG = IS_CLK_INVERTED;
  reg [0:0] IS_RSTM_INVERTED_REG = IS_RSTM_INVERTED;
  reg [31:0] MREG_REG = MREG;





  reg MREG_BIN;





  tri0 glblGSR = glbl.GSR;


  wire CEM_in;
  wire CLK_in;
  wire RSTM_in;
  wire [44:0] U_in;
  wire [44:0] V_in;








  












  assign CEM_in = (CEM !== 1'bz) && CEM; // rv 0
  assign CLK_in = (CLK !== 1'bz) && (CLK ^ IS_CLK_INVERTED_REG); // rv 0
  assign RSTM_in = (RSTM !== 1'bz) && (RSTM ^ IS_RSTM_INVERTED_REG); // rv 0
  assign U_in = U;
  assign V_in = V;




  reg attr_test;
  reg attr_err;

initial begin
  trig_attr = 1'b0;



  attr_test = 1'b0;

  attr_err = 1'b0;
  #1;
  trig_attr = ~trig_attr;
end






always @(trig_attr) begin
#1;
  MREG_BIN = MREG_REG[0];

end



  initial begin
    $display("Error: [Unisim %s-100] SIMPRIM primitive is not intended for direct instantiation in RTL or functional netlists. This primitive is only available in the SIMPRIM library for implemented netlists, please ensure you are pointing to the correct library. Instance %m", MODULE_NAME);
    #1 $finish;
  end



  always @(trig_attr) begin
  #1;
    if ((attr_test == 1'b1) ||
        ((MREG_REG != 1) &&
         (MREG_REG != 0))) begin
      $display("Error: [Unisim %s-103] MREG attribute is set to %d.  Legal values for this attribute are 1 or 0. Instance: %m", MODULE_NAME, MREG_REG);
      attr_err = 1'b1;
    end

    if (attr_err == 1'b1) #1 $finish;
  end






// begin behavioral model

  localparam M_WIDTH   = 45;
  reg [M_WIDTH-1:0] U_DATA_reg;
  reg [M_WIDTH-1:0] V_DATA_reg;

// initialize regs

initial begin
  U_DATA_reg = {1'b0, {M_WIDTH-1{1'b0}}};
  V_DATA_reg = {1'b0, {M_WIDTH-1{1'b0}}};
end


//*********************************************************
//*** Multiplier outputs U, V  with 1 level deep of register
//*********************************************************

   always @(posedge CLK_in) begin
      if  (RSTM_in || (MREG_BIN == 1'b0) || glblGSR) begin
         U_DATA_reg <= {1'b0, {M_WIDTH-1{1'b0}}};
         V_DATA_reg <= {1'b0, {M_WIDTH-1{1'b0}}};
      end else if (CEM_in)  begin
         U_DATA_reg <= U_in;
         V_DATA_reg <= V_in;
      end
   end

   assign U_DATA = (MREG_BIN == 1'b1) ? U_DATA_reg    : U_in;
   assign V_DATA = (MREG_BIN == 1'b1) ? V_DATA_reg    : V_in;

// end behavioral model










  specify
    (CLK => U_DATA[0]) = (0:0:0, 0:0:0);
    (CLK => U_DATA[10]) = (0:0:0, 0:0:0);
    (CLK => U_DATA[11]) = (0:0:0, 0:0:0);
    (CLK => U_DATA[12]) = (0:0:0, 0:0:0);
    (CLK => U_DATA[13]) = (0:0:0, 0:0:0);
    (CLK => U_DATA[14]) = (0:0:0, 0:0:0);
    (CLK => U_DATA[15]) = (0:0:0, 0:0:0);
    (CLK => U_DATA[16]) = (0:0:0, 0:0:0);
    (CLK => U_DATA[17]) = (0:0:0, 0:0:0);
    (CLK => U_DATA[18]) = (0:0:0, 0:0:0);
    (CLK => U_DATA[19]) = (0:0:0, 0:0:0);
    (CLK => U_DATA[1]) = (0:0:0, 0:0:0);
    (CLK => U_DATA[20]) = (0:0:0, 0:0:0);
    (CLK => U_DATA[21]) = (0:0:0, 0:0:0);
    (CLK => U_DATA[22]) = (0:0:0, 0:0:0);
    (CLK => U_DATA[23]) = (0:0:0, 0:0:0);
    (CLK => U_DATA[24]) = (0:0:0, 0:0:0);
    (CLK => U_DATA[25]) = (0:0:0, 0:0:0);
    (CLK => U_DATA[26]) = (0:0:0, 0:0:0);
    (CLK => U_DATA[27]) = (0:0:0, 0:0:0);
    (CLK => U_DATA[28]) = (0:0:0, 0:0:0);
    (CLK => U_DATA[29]) = (0:0:0, 0:0:0);
    (CLK => U_DATA[2]) = (0:0:0, 0:0:0);
    (CLK => U_DATA[30]) = (0:0:0, 0:0:0);
    (CLK => U_DATA[31]) = (0:0:0, 0:0:0);
    (CLK => U_DATA[32]) = (0:0:0, 0:0:0);
    (CLK => U_DATA[33]) = (0:0:0, 0:0:0);
    (CLK => U_DATA[34]) = (0:0:0, 0:0:0);
    (CLK => U_DATA[35]) = (0:0:0, 0:0:0);
    (CLK => U_DATA[36]) = (0:0:0, 0:0:0);
    (CLK => U_DATA[37]) = (0:0:0, 0:0:0);
    (CLK => U_DATA[38]) = (0:0:0, 0:0:0);
    (CLK => U_DATA[39]) = (0:0:0, 0:0:0);
    (CLK => U_DATA[3]) = (0:0:0, 0:0:0);
    (CLK => U_DATA[40]) = (0:0:0, 0:0:0);
    (CLK => U_DATA[41]) = (0:0:0, 0:0:0);
    (CLK => U_DATA[42]) = (0:0:0, 0:0:0);
    (CLK => U_DATA[43]) = (0:0:0, 0:0:0);
    (CLK => U_DATA[44]) = (0:0:0, 0:0:0);
    (CLK => U_DATA[4]) = (0:0:0, 0:0:0);
    (CLK => U_DATA[5]) = (0:0:0, 0:0:0);
    (CLK => U_DATA[6]) = (0:0:0, 0:0:0);
    (CLK => U_DATA[7]) = (0:0:0, 0:0:0);
    (CLK => U_DATA[8]) = (0:0:0, 0:0:0);
    (CLK => U_DATA[9]) = (0:0:0, 0:0:0);
    (CLK => V_DATA[0]) = (0:0:0, 0:0:0);
    (CLK => V_DATA[10]) = (0:0:0, 0:0:0);
    (CLK => V_DATA[11]) = (0:0:0, 0:0:0);
    (CLK => V_DATA[12]) = (0:0:0, 0:0:0);
    (CLK => V_DATA[13]) = (0:0:0, 0:0:0);
    (CLK => V_DATA[14]) = (0:0:0, 0:0:0);
    (CLK => V_DATA[15]) = (0:0:0, 0:0:0);
    (CLK => V_DATA[16]) = (0:0:0, 0:0:0);
    (CLK => V_DATA[17]) = (0:0:0, 0:0:0);
    (CLK => V_DATA[18]) = (0:0:0, 0:0:0);
    (CLK => V_DATA[19]) = (0:0:0, 0:0:0);
    (CLK => V_DATA[1]) = (0:0:0, 0:0:0);
    (CLK => V_DATA[20]) = (0:0:0, 0:0:0);
    (CLK => V_DATA[21]) = (0:0:0, 0:0:0);
    (CLK => V_DATA[22]) = (0:0:0, 0:0:0);
    (CLK => V_DATA[23]) = (0:0:0, 0:0:0);
    (CLK => V_DATA[24]) = (0:0:0, 0:0:0);
    (CLK => V_DATA[25]) = (0:0:0, 0:0:0);
    (CLK => V_DATA[26]) = (0:0:0, 0:0:0);
    (CLK => V_DATA[27]) = (0:0:0, 0:0:0);
    (CLK => V_DATA[28]) = (0:0:0, 0:0:0);
    (CLK => V_DATA[29]) = (0:0:0, 0:0:0);
    (CLK => V_DATA[2]) = (0:0:0, 0:0:0);
    (CLK => V_DATA[30]) = (0:0:0, 0:0:0);
    (CLK => V_DATA[31]) = (0:0:0, 0:0:0);
    (CLK => V_DATA[32]) = (0:0:0, 0:0:0);
    (CLK => V_DATA[33]) = (0:0:0, 0:0:0);
    (CLK => V_DATA[34]) = (0:0:0, 0:0:0);
    (CLK => V_DATA[35]) = (0:0:0, 0:0:0);
    (CLK => V_DATA[36]) = (0:0:0, 0:0:0);
    (CLK => V_DATA[37]) = (0:0:0, 0:0:0);
    (CLK => V_DATA[38]) = (0:0:0, 0:0:0);
    (CLK => V_DATA[39]) = (0:0:0, 0:0:0);
    (CLK => V_DATA[3]) = (0:0:0, 0:0:0);
    (CLK => V_DATA[40]) = (0:0:0, 0:0:0);
    (CLK => V_DATA[41]) = (0:0:0, 0:0:0);
    (CLK => V_DATA[42]) = (0:0:0, 0:0:0);
    (CLK => V_DATA[43]) = (0:0:0, 0:0:0);
    (CLK => V_DATA[44]) = (0:0:0, 0:0:0);
    (CLK => V_DATA[4]) = (0:0:0, 0:0:0);
    (CLK => V_DATA[5]) = (0:0:0, 0:0:0);
    (CLK => V_DATA[6]) = (0:0:0, 0:0:0);
    (CLK => V_DATA[7]) = (0:0:0, 0:0:0);
    (CLK => V_DATA[8]) = (0:0:0, 0:0:0);
    (CLK => V_DATA[9]) = (0:0:0, 0:0:0);
    (U[0] => U_DATA[0]) = (0:0:0, 0:0:0);
    (U[10] => U_DATA[10]) = (0:0:0, 0:0:0);
    (U[11] => U_DATA[11]) = (0:0:0, 0:0:0);
    (U[12] => U_DATA[12]) = (0:0:0, 0:0:0);
    (U[13] => U_DATA[13]) = (0:0:0, 0:0:0);
    (U[14] => U_DATA[14]) = (0:0:0, 0:0:0);
    (U[15] => U_DATA[15]) = (0:0:0, 0:0:0);
    (U[16] => U_DATA[16]) = (0:0:0, 0:0:0);
    (U[17] => U_DATA[17]) = (0:0:0, 0:0:0);
    (U[18] => U_DATA[18]) = (0:0:0, 0:0:0);
    (U[19] => U_DATA[19]) = (0:0:0, 0:0:0);
    (U[1] => U_DATA[1]) = (0:0:0, 0:0:0);
    (U[20] => U_DATA[20]) = (0:0:0, 0:0:0);
    (U[21] => U_DATA[21]) = (0:0:0, 0:0:0);
    (U[22] => U_DATA[22]) = (0:0:0, 0:0:0);
    (U[23] => U_DATA[23]) = (0:0:0, 0:0:0);
    (U[24] => U_DATA[24]) = (0:0:0, 0:0:0);
    (U[25] => U_DATA[25]) = (0:0:0, 0:0:0);
    (U[26] => U_DATA[26]) = (0:0:0, 0:0:0);
    (U[27] => U_DATA[27]) = (0:0:0, 0:0:0);
    (U[28] => U_DATA[28]) = (0:0:0, 0:0:0);
    (U[29] => U_DATA[29]) = (0:0:0, 0:0:0);
    (U[2] => U_DATA[2]) = (0:0:0, 0:0:0);
    (U[30] => U_DATA[30]) = (0:0:0, 0:0:0);
    (U[31] => U_DATA[31]) = (0:0:0, 0:0:0);
    (U[32] => U_DATA[32]) = (0:0:0, 0:0:0);
    (U[33] => U_DATA[33]) = (0:0:0, 0:0:0);
    (U[34] => U_DATA[34]) = (0:0:0, 0:0:0);
    (U[35] => U_DATA[35]) = (0:0:0, 0:0:0);
    (U[36] => U_DATA[36]) = (0:0:0, 0:0:0);
    (U[37] => U_DATA[37]) = (0:0:0, 0:0:0);
    (U[38] => U_DATA[38]) = (0:0:0, 0:0:0);
    (U[39] => U_DATA[39]) = (0:0:0, 0:0:0);
    (U[3] => U_DATA[3]) = (0:0:0, 0:0:0);
    (U[40] => U_DATA[40]) = (0:0:0, 0:0:0);
    (U[41] => U_DATA[41]) = (0:0:0, 0:0:0);
    (U[42] => U_DATA[42]) = (0:0:0, 0:0:0);
    (U[43] => U_DATA[43]) = (0:0:0, 0:0:0);
    (U[4] => U_DATA[4]) = (0:0:0, 0:0:0);
    (U[5] => U_DATA[5]) = (0:0:0, 0:0:0);
    (U[6] => U_DATA[6]) = (0:0:0, 0:0:0);
    (U[7] => U_DATA[7]) = (0:0:0, 0:0:0);
    (U[8] => U_DATA[8]) = (0:0:0, 0:0:0);
    (U[9] => U_DATA[9]) = (0:0:0, 0:0:0);
    (V[0] => V_DATA[0]) = (0:0:0, 0:0:0);
    (V[10] => V_DATA[10]) = (0:0:0, 0:0:0);
    (V[11] => V_DATA[11]) = (0:0:0, 0:0:0);
    (V[12] => V_DATA[12]) = (0:0:0, 0:0:0);
    (V[13] => V_DATA[13]) = (0:0:0, 0:0:0);
    (V[14] => V_DATA[14]) = (0:0:0, 0:0:0);
    (V[15] => V_DATA[15]) = (0:0:0, 0:0:0);
    (V[16] => V_DATA[16]) = (0:0:0, 0:0:0);
    (V[17] => V_DATA[17]) = (0:0:0, 0:0:0);
    (V[18] => V_DATA[18]) = (0:0:0, 0:0:0);
    (V[19] => V_DATA[19]) = (0:0:0, 0:0:0);
    (V[20] => V_DATA[20]) = (0:0:0, 0:0:0);
    (V[21] => V_DATA[21]) = (0:0:0, 0:0:0);
    (V[22] => V_DATA[22]) = (0:0:0, 0:0:0);
    (V[23] => V_DATA[23]) = (0:0:0, 0:0:0);
    (V[24] => V_DATA[24]) = (0:0:0, 0:0:0);
    (V[25] => V_DATA[25]) = (0:0:0, 0:0:0);
    (V[26] => V_DATA[26]) = (0:0:0, 0:0:0);
    (V[27] => V_DATA[27]) = (0:0:0, 0:0:0);
    (V[28] => V_DATA[28]) = (0:0:0, 0:0:0);
    (V[29] => V_DATA[29]) = (0:0:0, 0:0:0);
    (V[30] => V_DATA[30]) = (0:0:0, 0:0:0);
    (V[31] => V_DATA[31]) = (0:0:0, 0:0:0);
    (V[32] => V_DATA[32]) = (0:0:0, 0:0:0);
    (V[33] => V_DATA[33]) = (0:0:0, 0:0:0);
    (V[34] => V_DATA[34]) = (0:0:0, 0:0:0);
    (V[35] => V_DATA[35]) = (0:0:0, 0:0:0);
    (V[36] => V_DATA[36]) = (0:0:0, 0:0:0);
    (V[37] => V_DATA[37]) = (0:0:0, 0:0:0);
    (V[38] => V_DATA[38]) = (0:0:0, 0:0:0);
    (V[39] => V_DATA[39]) = (0:0:0, 0:0:0);
    (V[40] => V_DATA[40]) = (0:0:0, 0:0:0);
    (V[41] => V_DATA[41]) = (0:0:0, 0:0:0);
    (V[42] => V_DATA[42]) = (0:0:0, 0:0:0);
    (V[43] => V_DATA[43]) = (0:0:0, 0:0:0);
    (V[4] => V_DATA[4]) = (0:0:0, 0:0:0);
    (V[5] => V_DATA[5]) = (0:0:0, 0:0:0);
    (V[6] => V_DATA[6]) = (0:0:0, 0:0:0);
    (V[7] => V_DATA[7]) = (0:0:0, 0:0:0);
    (V[8] => V_DATA[8]) = (0:0:0, 0:0:0);
    (V[9] => V_DATA[9]) = (0:0:0, 0:0:0);






























































































































































































































































































































































    specparam PATHPULSE$ = 0;
  endspecify

endmodule

`endcelldefine
