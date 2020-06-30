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
// \   \   \/      Version     : 2018.1
//  \   \          Description : Xilinx Unified Simulation Library Component
//  /   /                        HBM_SNGLBLI_INTF_APB
// /___/   /\      Filename    : HBM_SNGLBLI_INTF_APB.v
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


module HBM_SNGLBLI_INTF_APB #(



  parameter CLK_SEL = "FALSE",
  parameter [0:0] IS_PCLK_INVERTED = 1'b0,
  parameter [0:0] IS_PRESET_N_INVERTED = 1'b0,
  parameter MC_ENABLE = "FALSE",
  parameter PHY_ENABLE = "FALSE",
  parameter PHY_PCLK_INVERT = "FALSE",
  parameter SWITCH_ENABLE = "FALSE"
)(
  output CATTRIP_PIPE,
  output [31:0] PRDATA_PIPE,
  output PREADY_PIPE,
  output PSLVERR_PIPE,
  output [2:0] TEMP_PIPE,

  input [21:0] PADDR,
  input PCLK,
  input PENABLE,
  input PRESET_N,
  input PSEL,
  input [31:0] PWDATA,
  input PWRITE
);

// define constants
  localparam MODULE_NAME = "HBM_SNGLBLI_INTF_APB";
  
// Parameter encodings and registers
  localparam CLK_SEL_FALSE = 0;
  localparam CLK_SEL_TRUE = 1;
  localparam MC_ENABLE_FALSE = 0;
  localparam MC_ENABLE_TRUE = 1;
  localparam PHY_ENABLE_FALSE = 0;
  localparam PHY_ENABLE_TRUE = 1;
  localparam SWITCH_ENABLE_FALSE = 0;
  localparam SWITCH_ENABLE_TRUE = 1;

  reg trig_attr;
// include dynamic registers - XILINX test only



  localparam [40:1] CLK_SEL_REG = CLK_SEL;
  localparam [0:0] IS_PCLK_INVERTED_REG = IS_PCLK_INVERTED;
  localparam [0:0] IS_PRESET_N_INVERTED_REG = IS_PRESET_N_INVERTED;
  localparam [40:1] MC_ENABLE_REG = MC_ENABLE;
  localparam [40:1] PHY_ENABLE_REG = PHY_ENABLE;
  localparam [40:1] PHY_PCLK_INVERT_REG = PHY_PCLK_INVERT;
  localparam [40:1] SWITCH_ENABLE_REG = SWITCH_ENABLE;








  reg CLK_SEL_BIN;
  reg MC_ENABLE_BIN;
  reg PHY_ENABLE_BIN;
  reg SWITCH_ENABLE_BIN;


  reg attr_test;
  reg attr_err;
  tri0 glblGSR = glbl.GSR;

  wire PCLK_in;
  wire PENABLE_in;
  wire PRESET_N_in;
  wire PSEL_in;
  wire PWRITE_in;
  wire [21:0] PADDR_in;
  wire [31:0] PWDATA_in;




















  assign PADDR_in = PADDR;
  assign PCLK_in = PCLK;
  assign PENABLE_in = PENABLE;
  assign PRESET_N_in = PRESET_N;
  assign PSEL_in = PSEL;
  assign PWDATA_in = PWDATA;
  assign PWRITE_in = PWRITE;



  initial begin
  trig_attr = 1'b0;
  


    attr_test = 1'b0;
  
    attr_err = 1'b0;
    #1;
    trig_attr = ~trig_attr;
  end
























  always @ (trig_attr) begin
  #1;
  CLK_SEL_BIN =
      (CLK_SEL_REG == "FALSE") ? CLK_SEL_FALSE :
      (CLK_SEL_REG == "TRUE") ? CLK_SEL_TRUE :
       CLK_SEL_FALSE;
  
  MC_ENABLE_BIN =
      (MC_ENABLE_REG == "FALSE") ? MC_ENABLE_FALSE :
      (MC_ENABLE_REG == "TRUE") ? MC_ENABLE_TRUE :
       MC_ENABLE_FALSE;
  
  PHY_ENABLE_BIN =
      (PHY_ENABLE_REG == "FALSE") ? PHY_ENABLE_FALSE :
      (PHY_ENABLE_REG == "TRUE") ? PHY_ENABLE_TRUE :
       PHY_ENABLE_FALSE;
  
  SWITCH_ENABLE_BIN =
      (SWITCH_ENABLE_REG == "FALSE") ? SWITCH_ENABLE_FALSE :
      (SWITCH_ENABLE_REG == "TRUE") ? SWITCH_ENABLE_TRUE :
       SWITCH_ENABLE_FALSE;
  
  end



  initial begin
    $display("Error: [Unisim %s-100] SIMPRIM primitive is not intended for direct instantiation in RTL or functional netlists. This primitive is only available in the SIMPRIM library for implemented netlists, please ensure you are pointing to the correct library. Instance %m", MODULE_NAME);
    #1 $finish;
  end



always @ (trig_attr) begin
  #1;
  if ((attr_test == 1'b1) ||
      ((CLK_SEL_REG != "FALSE") &&
       (CLK_SEL_REG != "TRUE"))) begin
    $display("Error: [Unisim %s-101] CLK_SEL attribute is set to %s.  Legal values for this attribute are FALSE or TRUE. Instance: %m", MODULE_NAME, CLK_SEL_REG);
    attr_err = 1'b1;
  end
  
  if ((attr_test == 1'b1) ||
      ((MC_ENABLE_REG != "FALSE") &&
       (MC_ENABLE_REG != "TRUE"))) begin
    $display("Error: [Unisim %s-104] MC_ENABLE attribute is set to %s.  Legal values for this attribute are FALSE or TRUE. Instance: %m", MODULE_NAME, MC_ENABLE_REG);
    attr_err = 1'b1;
  end
  
  if ((attr_test == 1'b1) ||
      ((PHY_ENABLE_REG != "FALSE") &&
       (PHY_ENABLE_REG != "TRUE"))) begin
    $display("Error: [Unisim %s-105] PHY_ENABLE attribute is set to %s.  Legal values for this attribute are FALSE or TRUE. Instance: %m", MODULE_NAME, PHY_ENABLE_REG);
    attr_err = 1'b1;
  end
  
  if ((attr_test == 1'b1) ||
      ((PHY_PCLK_INVERT_REG != "FALSE") &&
       (PHY_PCLK_INVERT_REG != "TRUE"))) begin
    $display("Error: [Unisim %s-106] PHY_PCLK_INVERT attribute is set to %s.  Legal values for this attribute are FALSE or TRUE. Instance: %m", MODULE_NAME, PHY_PCLK_INVERT_REG);
    attr_err = 1'b1;
  end
  
  if ((attr_test == 1'b1) ||
      ((SWITCH_ENABLE_REG != "FALSE") &&
       (SWITCH_ENABLE_REG != "TRUE"))) begin
    $display("Error: [Unisim %s-107] SWITCH_ENABLE attribute is set to %s.  Legal values for this attribute are FALSE or TRUE. Instance: %m", MODULE_NAME, SWITCH_ENABLE_REG);
    attr_err = 1'b1;
  end
  
  if (attr_err == 1'b1) #1 $finish;
end






// begin behavioral model

// end behavioral model


  specify
    (PCLK => CATTRIP_PIPE) = (100:100:100, 100:100:100);
    (PCLK => PRDATA_PIPE[0]) = (100:100:100, 100:100:100);
    (PCLK => PRDATA_PIPE[10]) = (100:100:100, 100:100:100);
    (PCLK => PRDATA_PIPE[11]) = (100:100:100, 100:100:100);
    (PCLK => PRDATA_PIPE[12]) = (100:100:100, 100:100:100);
    (PCLK => PRDATA_PIPE[13]) = (100:100:100, 100:100:100);
    (PCLK => PRDATA_PIPE[14]) = (100:100:100, 100:100:100);
    (PCLK => PRDATA_PIPE[15]) = (100:100:100, 100:100:100);
    (PCLK => PRDATA_PIPE[16]) = (100:100:100, 100:100:100);
    (PCLK => PRDATA_PIPE[17]) = (100:100:100, 100:100:100);
    (PCLK => PRDATA_PIPE[18]) = (100:100:100, 100:100:100);
    (PCLK => PRDATA_PIPE[19]) = (100:100:100, 100:100:100);
    (PCLK => PRDATA_PIPE[1]) = (100:100:100, 100:100:100);
    (PCLK => PRDATA_PIPE[20]) = (100:100:100, 100:100:100);
    (PCLK => PRDATA_PIPE[21]) = (100:100:100, 100:100:100);
    (PCLK => PRDATA_PIPE[22]) = (100:100:100, 100:100:100);
    (PCLK => PRDATA_PIPE[23]) = (100:100:100, 100:100:100);
    (PCLK => PRDATA_PIPE[24]) = (100:100:100, 100:100:100);
    (PCLK => PRDATA_PIPE[25]) = (100:100:100, 100:100:100);
    (PCLK => PRDATA_PIPE[26]) = (100:100:100, 100:100:100);
    (PCLK => PRDATA_PIPE[27]) = (100:100:100, 100:100:100);
    (PCLK => PRDATA_PIPE[28]) = (100:100:100, 100:100:100);
    (PCLK => PRDATA_PIPE[29]) = (100:100:100, 100:100:100);
    (PCLK => PRDATA_PIPE[2]) = (100:100:100, 100:100:100);
    (PCLK => PRDATA_PIPE[30]) = (100:100:100, 100:100:100);
    (PCLK => PRDATA_PIPE[31]) = (100:100:100, 100:100:100);
    (PCLK => PRDATA_PIPE[3]) = (100:100:100, 100:100:100);
    (PCLK => PRDATA_PIPE[4]) = (100:100:100, 100:100:100);
    (PCLK => PRDATA_PIPE[5]) = (100:100:100, 100:100:100);
    (PCLK => PRDATA_PIPE[6]) = (100:100:100, 100:100:100);
    (PCLK => PRDATA_PIPE[7]) = (100:100:100, 100:100:100);
    (PCLK => PRDATA_PIPE[8]) = (100:100:100, 100:100:100);
    (PCLK => PRDATA_PIPE[9]) = (100:100:100, 100:100:100);
    (PCLK => PREADY_PIPE) = (100:100:100, 100:100:100);
    (PCLK => PSLVERR_PIPE) = (100:100:100, 100:100:100);
    (PCLK => TEMP_PIPE[0]) = (100:100:100, 100:100:100);
    (PCLK => TEMP_PIPE[1]) = (100:100:100, 100:100:100);
    (PCLK => TEMP_PIPE[2]) = (100:100:100, 100:100:100);
    (negedge PRESET_N => (CATTRIP_PIPE +: 1)) = (100:100:100, 100:100:100);
    (negedge PRESET_N => (PRDATA_PIPE[0] +: 1)) = (100:100:100, 100:100:100);
    (negedge PRESET_N => (PRDATA_PIPE[10] +: 1)) = (100:100:100, 100:100:100);
    (negedge PRESET_N => (PRDATA_PIPE[11] +: 1)) = (100:100:100, 100:100:100);
    (negedge PRESET_N => (PRDATA_PIPE[12] +: 1)) = (100:100:100, 100:100:100);
    (negedge PRESET_N => (PRDATA_PIPE[13] +: 1)) = (100:100:100, 100:100:100);
    (negedge PRESET_N => (PRDATA_PIPE[14] +: 1)) = (100:100:100, 100:100:100);
    (negedge PRESET_N => (PRDATA_PIPE[15] +: 1)) = (100:100:100, 100:100:100);
    (negedge PRESET_N => (PRDATA_PIPE[16] +: 1)) = (100:100:100, 100:100:100);
    (negedge PRESET_N => (PRDATA_PIPE[17] +: 1)) = (100:100:100, 100:100:100);
    (negedge PRESET_N => (PRDATA_PIPE[18] +: 1)) = (100:100:100, 100:100:100);
    (negedge PRESET_N => (PRDATA_PIPE[19] +: 1)) = (100:100:100, 100:100:100);
    (negedge PRESET_N => (PRDATA_PIPE[1] +: 1)) = (100:100:100, 100:100:100);
    (negedge PRESET_N => (PRDATA_PIPE[20] +: 1)) = (100:100:100, 100:100:100);
    (negedge PRESET_N => (PRDATA_PIPE[21] +: 1)) = (100:100:100, 100:100:100);
    (negedge PRESET_N => (PRDATA_PIPE[22] +: 1)) = (100:100:100, 100:100:100);
    (negedge PRESET_N => (PRDATA_PIPE[23] +: 1)) = (100:100:100, 100:100:100);
    (negedge PRESET_N => (PRDATA_PIPE[24] +: 1)) = (100:100:100, 100:100:100);
    (negedge PRESET_N => (PRDATA_PIPE[25] +: 1)) = (100:100:100, 100:100:100);
    (negedge PRESET_N => (PRDATA_PIPE[26] +: 1)) = (100:100:100, 100:100:100);
    (negedge PRESET_N => (PRDATA_PIPE[27] +: 1)) = (100:100:100, 100:100:100);
    (negedge PRESET_N => (PRDATA_PIPE[28] +: 1)) = (100:100:100, 100:100:100);
    (negedge PRESET_N => (PRDATA_PIPE[29] +: 1)) = (100:100:100, 100:100:100);
    (negedge PRESET_N => (PRDATA_PIPE[2] +: 1)) = (100:100:100, 100:100:100);
    (negedge PRESET_N => (PRDATA_PIPE[30] +: 1)) = (100:100:100, 100:100:100);
    (negedge PRESET_N => (PRDATA_PIPE[31] +: 1)) = (100:100:100, 100:100:100);
    (negedge PRESET_N => (PRDATA_PIPE[3] +: 1)) = (100:100:100, 100:100:100);
    (negedge PRESET_N => (PRDATA_PIPE[4] +: 1)) = (100:100:100, 100:100:100);
    (negedge PRESET_N => (PRDATA_PIPE[5] +: 1)) = (100:100:100, 100:100:100);
    (negedge PRESET_N => (PRDATA_PIPE[6] +: 1)) = (100:100:100, 100:100:100);
    (negedge PRESET_N => (PRDATA_PIPE[7] +: 1)) = (100:100:100, 100:100:100);
    (negedge PRESET_N => (PRDATA_PIPE[8] +: 1)) = (100:100:100, 100:100:100);
    (negedge PRESET_N => (PRDATA_PIPE[9] +: 1)) = (100:100:100, 100:100:100);
    (negedge PRESET_N => (PREADY_PIPE +: 1)) = (100:100:100, 100:100:100);
    (negedge PRESET_N => (PSLVERR_PIPE +: 1)) = (100:100:100, 100:100:100);
    (negedge PRESET_N => (TEMP_PIPE[0] +: 1)) = (100:100:100, 100:100:100);
    (negedge PRESET_N => (TEMP_PIPE[1] +: 1)) = (100:100:100, 100:100:100);
    (negedge PRESET_N => (TEMP_PIPE[2] +: 1)) = (100:100:100, 100:100:100);
    (posedge PRESET_N => (CATTRIP_PIPE +: 1)) = (100:100:100, 100:100:100);
    (posedge PRESET_N => (PRDATA_PIPE[0] +: 1)) = (100:100:100, 100:100:100);
    (posedge PRESET_N => (PRDATA_PIPE[10] +: 1)) = (100:100:100, 100:100:100);
    (posedge PRESET_N => (PRDATA_PIPE[11] +: 1)) = (100:100:100, 100:100:100);
    (posedge PRESET_N => (PRDATA_PIPE[12] +: 1)) = (100:100:100, 100:100:100);
    (posedge PRESET_N => (PRDATA_PIPE[13] +: 1)) = (100:100:100, 100:100:100);
    (posedge PRESET_N => (PRDATA_PIPE[14] +: 1)) = (100:100:100, 100:100:100);
    (posedge PRESET_N => (PRDATA_PIPE[15] +: 1)) = (100:100:100, 100:100:100);
    (posedge PRESET_N => (PRDATA_PIPE[16] +: 1)) = (100:100:100, 100:100:100);
    (posedge PRESET_N => (PRDATA_PIPE[17] +: 1)) = (100:100:100, 100:100:100);
    (posedge PRESET_N => (PRDATA_PIPE[18] +: 1)) = (100:100:100, 100:100:100);
    (posedge PRESET_N => (PRDATA_PIPE[19] +: 1)) = (100:100:100, 100:100:100);
    (posedge PRESET_N => (PRDATA_PIPE[1] +: 1)) = (100:100:100, 100:100:100);
    (posedge PRESET_N => (PRDATA_PIPE[20] +: 1)) = (100:100:100, 100:100:100);
    (posedge PRESET_N => (PRDATA_PIPE[21] +: 1)) = (100:100:100, 100:100:100);
    (posedge PRESET_N => (PRDATA_PIPE[22] +: 1)) = (100:100:100, 100:100:100);
    (posedge PRESET_N => (PRDATA_PIPE[23] +: 1)) = (100:100:100, 100:100:100);
    (posedge PRESET_N => (PRDATA_PIPE[24] +: 1)) = (100:100:100, 100:100:100);
    (posedge PRESET_N => (PRDATA_PIPE[25] +: 1)) = (100:100:100, 100:100:100);
    (posedge PRESET_N => (PRDATA_PIPE[26] +: 1)) = (100:100:100, 100:100:100);
    (posedge PRESET_N => (PRDATA_PIPE[27] +: 1)) = (100:100:100, 100:100:100);
    (posedge PRESET_N => (PRDATA_PIPE[28] +: 1)) = (100:100:100, 100:100:100);
    (posedge PRESET_N => (PRDATA_PIPE[29] +: 1)) = (100:100:100, 100:100:100);
    (posedge PRESET_N => (PRDATA_PIPE[2] +: 1)) = (100:100:100, 100:100:100);
    (posedge PRESET_N => (PRDATA_PIPE[30] +: 1)) = (100:100:100, 100:100:100);
    (posedge PRESET_N => (PRDATA_PIPE[31] +: 1)) = (100:100:100, 100:100:100);
    (posedge PRESET_N => (PRDATA_PIPE[3] +: 1)) = (100:100:100, 100:100:100);
    (posedge PRESET_N => (PRDATA_PIPE[4] +: 1)) = (100:100:100, 100:100:100);
    (posedge PRESET_N => (PRDATA_PIPE[5] +: 1)) = (100:100:100, 100:100:100);
    (posedge PRESET_N => (PRDATA_PIPE[6] +: 1)) = (100:100:100, 100:100:100);
    (posedge PRESET_N => (PRDATA_PIPE[7] +: 1)) = (100:100:100, 100:100:100);
    (posedge PRESET_N => (PRDATA_PIPE[8] +: 1)) = (100:100:100, 100:100:100);
    (posedge PRESET_N => (PRDATA_PIPE[9] +: 1)) = (100:100:100, 100:100:100);
    (posedge PRESET_N => (PREADY_PIPE +: 1)) = (100:100:100, 100:100:100);
    (posedge PRESET_N => (PSLVERR_PIPE +: 1)) = (100:100:100, 100:100:100);
    (posedge PRESET_N => (TEMP_PIPE[0] +: 1)) = (100:100:100, 100:100:100);
    (posedge PRESET_N => (TEMP_PIPE[1] +: 1)) = (100:100:100, 100:100:100);
    (posedge PRESET_N => (TEMP_PIPE[2] +: 1)) = (100:100:100, 100:100:100);










































































































































































































































    specparam PATHPULSE$ = 0;
  endspecify

endmodule

`endcelldefine

