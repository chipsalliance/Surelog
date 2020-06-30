///////////////////////////////////////////////////////////////////////////////
//     Copyright (c) 1995/2019 Xilinx, Inc.
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
// \   \   \/      Version     : 2020.1
//  \   \          Description : Xilinx Unified Simulation Library Component
//  /   /                        RFADC
// /___/   /\      Filename    : RFADC.v
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

module RFADC #(
`ifdef XIL_TIMING
  parameter LOC = "UNPLACED",
`endif
  parameter integer OPT_ANALOG = 0,
  parameter integer OPT_CLK_DIST = 0,
  parameter SIM_DEVICE = "ULTRASCALE_PLUS",
  parameter integer XPA_ACTIVE_DUTYCYCLE = 100,
  parameter integer XPA_CFG0 = 0,
  parameter integer XPA_CFG1 = 0,
  parameter integer XPA_CFG2 = 0,
  parameter XPA_NUM_ADCS = "0",
  parameter integer XPA_NUM_DDCS = 0,
  parameter XPA_PLL_USED = "EXTERNAL",
  parameter integer XPA_SAMPLE_RATE_MSPS = 0
)(
  output CLK_ADC,
  output CLK_DIST_OUT_NORTH,
  output CLK_DIST_OUT_SOUTH,
  output [191:0] DATA_ADC0,
  output [191:0] DATA_ADC1,
  output [191:0] DATA_ADC2,
  output [191:0] DATA_ADC3,
  output [15:0] DOUT,
  output DRDY,
  output PLL_DMON_OUT,
  output PLL_REFCLK_OUT,
  output [23:0] STATUS_ADC0,
  output [23:0] STATUS_ADC1,
  output [23:0] STATUS_ADC2,
  output [23:0] STATUS_ADC3,
  output [23:0] STATUS_COMMON,
  output SYSREF_OUT_NORTH,
  output SYSREF_OUT_SOUTH,
  output T1_ALLOWED_SOUTH,

  input ADC_CLK_N,
  input ADC_CLK_P,
  input CLK_DIST_IN_NORTH,
  input CLK_DIST_IN_SOUTH,
  input CLK_FIFO_LM,
  input [15:0] CONTROL_ADC0,
  input [15:0] CONTROL_ADC1,
  input [15:0] CONTROL_ADC2,
  input [15:0] CONTROL_ADC3,
  input [15:0] CONTROL_COMMON,
  input [11:0] DADDR,
  input DCLK,
  input DEN,
  input [15:0] DI,
  input DWE,
  input FABRIC_CLK,
  input PLL_MONCLK,
  input PLL_REFCLK_IN,
  input SYSREF_IN_NORTH,
  input SYSREF_IN_SOUTH,
  input SYSREF_N,
  input SYSREF_P,
  input T1_ALLOWED_NORTH,
  input VIN0_N,
  input VIN0_P,
  input VIN1_N,
  input VIN1_P,
  input VIN2_N,
  input VIN2_P,
  input VIN3_N,
  input VIN3_P,
  input VIN_I01_N,
  input VIN_I01_P,
  input VIN_I23_N,
  input VIN_I23_P
);

// define constants
  localparam MODULE_NAME = "RFADC";
  
  reg trig_attr;
// include dynamic registers - XILINX test only
`ifdef XIL_DR
  `include "RFADC_dr.v"
`else
  reg [15:0] OPT_ANALOG_REG = OPT_ANALOG;
  reg [15:0] OPT_CLK_DIST_REG = OPT_CLK_DIST;
  reg [152:1] SIM_DEVICE_REG = SIM_DEVICE;
  reg [6:0] XPA_ACTIVE_DUTYCYCLE_REG = XPA_ACTIVE_DUTYCYCLE;
  reg [15:0] XPA_CFG0_REG = XPA_CFG0;
  reg [15:0] XPA_CFG1_REG = XPA_CFG1;
  reg [15:0] XPA_CFG2_REG = XPA_CFG2;
  reg [16:1] XPA_NUM_ADCS_REG = XPA_NUM_ADCS;
  reg [2:0] XPA_NUM_DDCS_REG = XPA_NUM_DDCS;
  reg [112:1] XPA_PLL_USED_REG = XPA_PLL_USED;
  reg [13:0] XPA_SAMPLE_RATE_MSPS_REG = XPA_SAMPLE_RATE_MSPS;
`endif

`ifdef XIL_XECLIB
reg glblGSR = 1'b0;
`else
tri0 glblGSR = glbl.GSR;
`endif

  wire CLK_ADC_SPARE_out;
  wire CLK_ADC_out;
  wire CLK_DIST_OUT_NORTH_out;
  wire CLK_DIST_OUT_SOUTH_out;
  wire DRDY_out;
  wire PLL_DMON_OUT_out;
  wire PLL_REFCLK_OUT_out;
  wire SYSREF_OUT_NORTH_out;
  wire SYSREF_OUT_SOUTH_out;
  wire T1_ALLOWED_SOUTH_out;
  wire [15:0] DOUT_out;
  wire [15:0] TEST_STATUS_out;
  wire [191:0] DATA_ADC0_out;
  wire [191:0] DATA_ADC1_out;
  wire [191:0] DATA_ADC2_out;
  wire [191:0] DATA_ADC3_out;
  wire [1:0] PLL_SCAN_OUT_B_FD_out;
  wire [23:0] STATUS_ADC0_out;
  wire [23:0] STATUS_ADC1_out;
  wire [23:0] STATUS_ADC2_out;
  wire [23:0] STATUS_ADC3_out;
  wire [23:0] STATUS_COMMON_out;
  wire [299:0] TEST_SO_out;

  wire ADC_CLK_N_in;
  wire ADC_CLK_P_in;
  wire CLK_DIST_IN_NORTH_in;
  wire CLK_DIST_IN_SOUTH_in;
  wire CLK_FIFO_LM_in;
  wire DCLK_in;
  wire DEN_in;
  wire DWE_in;
  wire FABRIC_CLK_in;
  wire PLL_MONCLK_in;
  wire PLL_REFCLK_IN_in;
  wire PLL_SCAN_EN_B_FD_in;
  wire PLL_SCAN_MODE_B_FD_in;
  wire PLL_SCAN_RST_EN_FD_in;
  wire SYSREF_IN_NORTH_in;
  wire SYSREF_IN_SOUTH_in;
  wire SYSREF_N_in;
  wire SYSREF_P_in;
  wire T1_ALLOWED_NORTH_in;
  wire TEST_SCAN_MODE_B_in;
  wire TEST_SCAN_RESET_in;
  wire TEST_SE_B_in;
  wire VIN0_N_in;
  wire VIN0_P_in;
  wire VIN1_N_in;
  wire VIN1_P_in;
  wire VIN2_N_in;
  wire VIN2_P_in;
  wire VIN3_N_in;
  wire VIN3_P_in;
  wire VIN_I01_N_in;
  wire VIN_I01_P_in;
  wire VIN_I23_N_in;
  wire VIN_I23_P_in;
  wire [11:0] DADDR_in;
  wire [15:0] CONTROL_ADC0_in;
  wire [15:0] CONTROL_ADC1_in;
  wire [15:0] CONTROL_ADC2_in;
  wire [15:0] CONTROL_ADC3_in;
  wire [15:0] CONTROL_COMMON_in;
  wire [15:0] DI_in;
  wire [15:0] TEST_SCAN_CTRL_in;
  wire [1:0] PLL_SCAN_CLK_FD_in;
  wire [1:0] PLL_SCAN_IN_FD_in;
  wire [299:0] TEST_SI_in;
  wire [4:0] TEST_SCAN_CLK_in;

`ifdef XIL_TIMING
  wire DCLK_delay;
  wire DEN_delay;
  wire DWE_delay;
  wire FABRIC_CLK_delay;
  wire [11:0] DADDR_delay;
  wire [15:0] CONTROL_ADC0_delay;
  wire [15:0] CONTROL_ADC1_delay;
  wire [15:0] CONTROL_ADC2_delay;
  wire [15:0] CONTROL_ADC3_delay;
  wire [15:0] CONTROL_COMMON_delay;
  wire [15:0] DI_delay;
`endif

  real VIN0_N_real = 1.0;
  real VIN0_P_real = 1.0;
  real VIN1_N_real = 1.0;
  real VIN1_P_real = 1.0;
  real VIN2_N_real = 1.0;
  real VIN2_P_real = 1.0;
  real VIN3_N_real = 1.0;
  real VIN3_P_real = 1.0;
  real VIN_I01_N_real = 1.0;
  real VIN_I01_P_real = 1.0;
  real VIN_I23_N_real = 1.0;
  real VIN_I23_P_real = 1.0;

  assign CLK_ADC = CLK_ADC_out;
  assign CLK_DIST_OUT_NORTH = CLK_DIST_OUT_NORTH_out;
  assign CLK_DIST_OUT_SOUTH = CLK_DIST_OUT_SOUTH_out;
  assign DATA_ADC0 = DATA_ADC0_out;
  assign DATA_ADC1 = DATA_ADC1_out;
  assign DATA_ADC2 = DATA_ADC2_out;
  assign DATA_ADC3 = DATA_ADC3_out;
  assign DOUT = DOUT_out;
  assign DRDY = DRDY_out;
  assign PLL_DMON_OUT = PLL_DMON_OUT_out;
  assign PLL_REFCLK_OUT = PLL_REFCLK_OUT_out;
  assign STATUS_ADC0 = STATUS_ADC0_out;
  assign STATUS_ADC1 = STATUS_ADC1_out;
  assign STATUS_ADC2 = STATUS_ADC2_out;
  assign STATUS_ADC3 = STATUS_ADC3_out;
  assign STATUS_COMMON = STATUS_COMMON_out;
  assign SYSREF_OUT_NORTH = SYSREF_OUT_NORTH_out;
  assign SYSREF_OUT_SOUTH = SYSREF_OUT_SOUTH_out;
  assign T1_ALLOWED_SOUTH = T1_ALLOWED_SOUTH_out;

`ifdef XIL_TIMING
  assign CONTROL_ADC0_in = CONTROL_ADC0_delay;
  assign CONTROL_ADC1_in = CONTROL_ADC1_delay;
  assign CONTROL_ADC2_in = CONTROL_ADC2_delay;
  assign CONTROL_ADC3_in = CONTROL_ADC3_delay;
  assign CONTROL_COMMON_in = CONTROL_COMMON_delay;
  assign DADDR_in = DADDR_delay;
  assign DCLK_in = DCLK_delay;
  assign DEN_in = DEN_delay;
  assign DI_in = DI_delay;
  assign DWE_in = DWE_delay;
  assign FABRIC_CLK_in = FABRIC_CLK_delay;
`else
  assign CONTROL_ADC0_in = CONTROL_ADC0;
  assign CONTROL_ADC1_in = CONTROL_ADC1;
  assign CONTROL_ADC2_in = CONTROL_ADC2;
  assign CONTROL_ADC3_in = CONTROL_ADC3;
  assign CONTROL_COMMON_in = CONTROL_COMMON;
  assign DADDR_in = DADDR;
  assign DCLK_in = DCLK;
  assign DEN_in = DEN;
  assign DI_in = DI;
  assign DWE_in = DWE;
  assign FABRIC_CLK_in = FABRIC_CLK;
`endif

  assign ADC_CLK_N_in = ADC_CLK_N;
  assign ADC_CLK_P_in = ADC_CLK_P;
  assign CLK_DIST_IN_NORTH_in = CLK_DIST_IN_NORTH;
  assign CLK_DIST_IN_SOUTH_in = CLK_DIST_IN_SOUTH;
  assign CLK_FIFO_LM_in = CLK_FIFO_LM;
  assign PLL_MONCLK_in = PLL_MONCLK;
  assign PLL_REFCLK_IN_in = PLL_REFCLK_IN;
  assign SYSREF_IN_NORTH_in = SYSREF_IN_NORTH;
  assign SYSREF_IN_SOUTH_in = SYSREF_IN_SOUTH;
  assign SYSREF_N_in = SYSREF_N;
  assign SYSREF_P_in = SYSREF_P;
  assign T1_ALLOWED_NORTH_in = T1_ALLOWED_NORTH;
  assign VIN0_N_in = VIN0_N;
  assign VIN0_P_in = VIN0_P;
  assign VIN1_N_in = VIN1_N;
  assign VIN1_P_in = VIN1_P;
  assign VIN2_N_in = VIN2_N;
  assign VIN2_P_in = VIN2_P;
  assign VIN3_N_in = VIN3_N;
  assign VIN3_P_in = VIN3_P;
  assign VIN_I01_N_in = VIN_I01_N;
  assign VIN_I01_P_in = VIN_I01_P;
  assign VIN_I23_N_in = VIN_I23_N;
  assign VIN_I23_P_in = VIN_I23_P;

`ifndef XIL_XECLIB
  reg attr_test;
  reg attr_err;
  
  initial begin
  trig_attr = 1'b0;
  `ifdef XIL_ATTR_TEST
    attr_test = 1'b1;
  `else
    attr_test = 1'b0;
  `endif
    attr_err = 1'b0;
    #1;
    trig_attr = ~trig_attr;
  end
`endif

`ifndef XIL_XECLIB
  always @ (trig_attr) begin
    #1;
    if ((attr_test == 1'b1) ||
        ((OPT_ANALOG_REG < 0) || (OPT_ANALOG_REG > 65535))) begin
      $display("Error: [Unisim %s-101] OPT_ANALOG attribute is set to %d.  Legal values for this attribute are 0 to 65535. Instance: %m", MODULE_NAME, OPT_ANALOG_REG);
      attr_err = 1'b1;
    end
    
    if ((attr_test == 1'b1) ||
        ((OPT_CLK_DIST_REG < 0) || (OPT_CLK_DIST_REG > 65535))) begin
      $display("Error: [Unisim %s-102] OPT_CLK_DIST attribute is set to %d.  Legal values for this attribute are 0 to 65535. Instance: %m", MODULE_NAME, OPT_CLK_DIST_REG);
      attr_err = 1'b1;
    end
    
    if ((attr_test == 1'b1) ||
        ((SIM_DEVICE_REG != "ULTRASCALE_PLUS") &&
         (SIM_DEVICE_REG != "ULTRASCALE_PLUS_ES1") &&
         (SIM_DEVICE_REG != "ULTRASCALE_PLUS_ES2"))) begin
      $display("Error: [Unisim %s-103] SIM_DEVICE attribute is set to %s.  Legal values for this attribute are ULTRASCALE_PLUS, ULTRASCALE_PLUS_ES1 or ULTRASCALE_PLUS_ES2. Instance: %m", MODULE_NAME, SIM_DEVICE_REG);
      attr_err = 1'b1;
    end
    
    if ((attr_test == 1'b1) ||
        ((XPA_ACTIVE_DUTYCYCLE_REG < 0) || (XPA_ACTIVE_DUTYCYCLE_REG > 100))) begin
      $display("Error: [Unisim %s-104] XPA_ACTIVE_DUTYCYCLE attribute is set to %d.  Legal values for this attribute are 0 to 100. Instance: %m", MODULE_NAME, XPA_ACTIVE_DUTYCYCLE_REG);
      attr_err = 1'b1;
    end
    
    if ((attr_test == 1'b1) ||
        ((XPA_CFG0_REG < 0) || (XPA_CFG0_REG > 65535))) begin
      $display("Error: [Unisim %s-105] XPA_CFG0 attribute is set to %d.  Legal values for this attribute are 0 to 65535. Instance: %m", MODULE_NAME, XPA_CFG0_REG);
      attr_err = 1'b1;
    end
    
    if ((attr_test == 1'b1) ||
        ((XPA_CFG1_REG < 0) || (XPA_CFG1_REG > 65535))) begin
      $display("Error: [Unisim %s-106] XPA_CFG1 attribute is set to %d.  Legal values for this attribute are 0 to 65535. Instance: %m", MODULE_NAME, XPA_CFG1_REG);
      attr_err = 1'b1;
    end
    
    if ((attr_test == 1'b1) ||
        ((XPA_CFG2_REG < 0) || (XPA_CFG2_REG > 65535))) begin
      $display("Error: [Unisim %s-107] XPA_CFG2 attribute is set to %d.  Legal values for this attribute are 0 to 65535. Instance: %m", MODULE_NAME, XPA_CFG2_REG);
      attr_err = 1'b1;
    end
    
    if ((attr_test == 1'b1) ||
        ((XPA_NUM_ADCS_REG != "0") &&
         (XPA_NUM_ADCS_REG != "1") &&
         (XPA_NUM_ADCS_REG != "1I") &&
         (XPA_NUM_ADCS_REG != "2") &&
         (XPA_NUM_ADCS_REG != "2I") &&
         (XPA_NUM_ADCS_REG != "3") &&
         (XPA_NUM_ADCS_REG != "4"))) begin
      $display("Error: [Unisim %s-108] XPA_NUM_ADCS attribute is set to %s.  Legal values for this attribute are 0, 1, 1I, 2, 2I, 3 or 4. Instance: %m", MODULE_NAME, XPA_NUM_ADCS_REG);
      attr_err = 1'b1;
    end
    
    if ((attr_test == 1'b1) ||
        ((XPA_NUM_DDCS_REG < 0) || (XPA_NUM_DDCS_REG > 4))) begin
      $display("Error: [Unisim %s-109] XPA_NUM_DDCS attribute is set to %d.  Legal values for this attribute are 0 to 4. Instance: %m", MODULE_NAME, XPA_NUM_DDCS_REG);
      attr_err = 1'b1;
    end
    
    if ((attr_test == 1'b1) ||
        ((XPA_PLL_USED_REG != "EXTERNAL") &&
         (XPA_PLL_USED_REG != "DISTRIBUTED_T1") &&
         (XPA_PLL_USED_REG != "INTERNAL_PLL"))) begin
      $display("Error: [Unisim %s-110] XPA_PLL_USED attribute is set to %s.  Legal values for this attribute are EXTERNAL, DISTRIBUTED_T1 or INTERNAL_PLL. Instance: %m", MODULE_NAME, XPA_PLL_USED_REG);
      attr_err = 1'b1;
    end
    
    if ((attr_test == 1'b1) ||
        ((XPA_SAMPLE_RATE_MSPS_REG < 0) || (XPA_SAMPLE_RATE_MSPS_REG > 10000))) begin
      $display("Error: [Unisim %s-111] XPA_SAMPLE_RATE_MSPS attribute is set to %d.  Legal values for this attribute are 0 to 10000. Instance: %m", MODULE_NAME, XPA_SAMPLE_RATE_MSPS_REG);
      attr_err = 1'b1;
    end
    
    if (attr_err == 1'b1) #1 $finish;
  end
`endif


assign PLL_SCAN_CLK_FD_in = 2'b11; // tie off
assign TEST_SCAN_CLK_in = 5'b11111; // tie off

assign PLL_SCAN_EN_B_FD_in = 1'b1; // tie off
assign PLL_SCAN_IN_FD_in = 2'b11; // tie off
assign PLL_SCAN_MODE_B_FD_in = 1'b1; // tie off
assign PLL_SCAN_RST_EN_FD_in = 1'b1; // tie off
assign TEST_SCAN_CTRL_in = 16'b1111111111111111; // tie off
assign TEST_SCAN_MODE_B_in = 1'b1; // tie off
assign TEST_SCAN_RESET_in = 1'b1; // tie off
assign TEST_SE_B_in = 1'b1; // tie off
assign TEST_SI_in = 300'b111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111; // tie off

  SIP_RFADC SIP_RFADC_INST (
    .OPT_ANALOG (OPT_ANALOG_REG),
    .OPT_CLK_DIST (OPT_CLK_DIST_REG),
    .SIM_DEVICE (SIM_DEVICE_REG),
    .XPA_ACTIVE_DUTYCYCLE (XPA_ACTIVE_DUTYCYCLE_REG),
    .XPA_CFG0 (XPA_CFG0_REG),
    .XPA_CFG1 (XPA_CFG1_REG),
    .XPA_CFG2 (XPA_CFG2_REG),
    .XPA_NUM_ADCS (XPA_NUM_ADCS_REG),
    .XPA_NUM_DDCS (XPA_NUM_DDCS_REG),
    .XPA_PLL_USED (XPA_PLL_USED_REG),
    .XPA_SAMPLE_RATE_MSPS (XPA_SAMPLE_RATE_MSPS_REG),
    .CLK_ADC (CLK_ADC_out),
    .CLK_ADC_SPARE (CLK_ADC_SPARE_out),
    .CLK_DIST_OUT_NORTH (CLK_DIST_OUT_NORTH_out),
    .CLK_DIST_OUT_SOUTH (CLK_DIST_OUT_SOUTH_out),
    .DATA_ADC0 (DATA_ADC0_out),
    .DATA_ADC1 (DATA_ADC1_out),
    .DATA_ADC2 (DATA_ADC2_out),
    .DATA_ADC3 (DATA_ADC3_out),
    .DOUT (DOUT_out),
    .DRDY (DRDY_out),
    .PLL_DMON_OUT (PLL_DMON_OUT_out),
    .PLL_REFCLK_OUT (PLL_REFCLK_OUT_out),
    .PLL_SCAN_OUT_B_FD (PLL_SCAN_OUT_B_FD_out),
    .STATUS_ADC0 (STATUS_ADC0_out),
    .STATUS_ADC1 (STATUS_ADC1_out),
    .STATUS_ADC2 (STATUS_ADC2_out),
    .STATUS_ADC3 (STATUS_ADC3_out),
    .STATUS_COMMON (STATUS_COMMON_out),
    .SYSREF_OUT_NORTH (SYSREF_OUT_NORTH_out),
    .SYSREF_OUT_SOUTH (SYSREF_OUT_SOUTH_out),
    .T1_ALLOWED_SOUTH (T1_ALLOWED_SOUTH_out),
    .TEST_SO (TEST_SO_out),
    .TEST_STATUS (TEST_STATUS_out),
    .ADC_CLK_N (ADC_CLK_N_in),
    .ADC_CLK_P (ADC_CLK_P_in),
    .CLK_DIST_IN_NORTH (CLK_DIST_IN_NORTH_in),
    .CLK_DIST_IN_SOUTH (CLK_DIST_IN_SOUTH_in),
    .CLK_FIFO_LM (CLK_FIFO_LM_in),
    .CONTROL_ADC0 (CONTROL_ADC0_in),
    .CONTROL_ADC1 (CONTROL_ADC1_in),
    .CONTROL_ADC2 (CONTROL_ADC2_in),
    .CONTROL_ADC3 (CONTROL_ADC3_in),
    .CONTROL_COMMON (CONTROL_COMMON_in),
    .DADDR (DADDR_in),
    .DCLK (DCLK_in),
    .DEN (DEN_in),
    .DI (DI_in),
    .DWE (DWE_in),
    .FABRIC_CLK (FABRIC_CLK_in),
    .PLL_MONCLK (PLL_MONCLK_in),
    .PLL_REFCLK_IN (PLL_REFCLK_IN_in),
    .PLL_SCAN_CLK_FD (PLL_SCAN_CLK_FD_in),
    .PLL_SCAN_EN_B_FD (PLL_SCAN_EN_B_FD_in),
    .PLL_SCAN_IN_FD (PLL_SCAN_IN_FD_in),
    .PLL_SCAN_MODE_B_FD (PLL_SCAN_MODE_B_FD_in),
    .PLL_SCAN_RST_EN_FD (PLL_SCAN_RST_EN_FD_in),
    .SYSREF_IN_NORTH (SYSREF_IN_NORTH_in),
    .SYSREF_IN_SOUTH (SYSREF_IN_SOUTH_in),
    .SYSREF_N (SYSREF_N_in),
    .SYSREF_P (SYSREF_P_in),
    .T1_ALLOWED_NORTH (T1_ALLOWED_NORTH_in),
    .TEST_SCAN_CLK (TEST_SCAN_CLK_in),
    .TEST_SCAN_CTRL (TEST_SCAN_CTRL_in),
    .TEST_SCAN_MODE_B (TEST_SCAN_MODE_B_in),
    .TEST_SCAN_RESET (TEST_SCAN_RESET_in),
    .TEST_SE_B (TEST_SE_B_in),
    .TEST_SI (TEST_SI_in),
    .VIN0_N (VIN0_N_real),
    .VIN0_P (VIN0_P_real),
    .VIN1_N (VIN1_N_real),
    .VIN1_P (VIN1_P_real),
    .VIN2_N (VIN2_N_real),
    .VIN2_P (VIN2_P_real),
    .VIN3_N (VIN3_N_real),
    .VIN3_P (VIN3_P_real),
    .VIN_I01_N (VIN_I01_N_real),
    .VIN_I01_P (VIN_I01_P_real),
    .VIN_I23_N (VIN_I23_N_real),
    .VIN_I23_P (VIN_I23_P_real),
    .GSR (glblGSR)
  );

`ifdef XIL_TIMING
  reg notifier;
`endif

`ifndef XIL_XECLIB
  specify
    (CLK_FIFO_LM => DATA_ADC0[0]) = (0:0:0, 0:0:0);
    (CLK_FIFO_LM => DATA_ADC0[100]) = (0:0:0, 0:0:0);
    (CLK_FIFO_LM => DATA_ADC0[101]) = (0:0:0, 0:0:0);
    (CLK_FIFO_LM => DATA_ADC0[102]) = (0:0:0, 0:0:0);
    (CLK_FIFO_LM => DATA_ADC0[103]) = (0:0:0, 0:0:0);
    (CLK_FIFO_LM => DATA_ADC0[104]) = (0:0:0, 0:0:0);
    (CLK_FIFO_LM => DATA_ADC0[105]) = (0:0:0, 0:0:0);
    (CLK_FIFO_LM => DATA_ADC0[106]) = (0:0:0, 0:0:0);
    (CLK_FIFO_LM => DATA_ADC0[107]) = (0:0:0, 0:0:0);
    (CLK_FIFO_LM => DATA_ADC0[108]) = (0:0:0, 0:0:0);
    (CLK_FIFO_LM => DATA_ADC0[109]) = (0:0:0, 0:0:0);
    (CLK_FIFO_LM => DATA_ADC0[10]) = (0:0:0, 0:0:0);
    (CLK_FIFO_LM => DATA_ADC0[110]) = (0:0:0, 0:0:0);
    (CLK_FIFO_LM => DATA_ADC0[111]) = (0:0:0, 0:0:0);
    (CLK_FIFO_LM => DATA_ADC0[112]) = (0:0:0, 0:0:0);
    (CLK_FIFO_LM => DATA_ADC0[113]) = (0:0:0, 0:0:0);
    (CLK_FIFO_LM => DATA_ADC0[114]) = (0:0:0, 0:0:0);
    (CLK_FIFO_LM => DATA_ADC0[115]) = (0:0:0, 0:0:0);
    (CLK_FIFO_LM => DATA_ADC0[116]) = (0:0:0, 0:0:0);
    (CLK_FIFO_LM => DATA_ADC0[117]) = (0:0:0, 0:0:0);
    (CLK_FIFO_LM => DATA_ADC0[118]) = (0:0:0, 0:0:0);
    (CLK_FIFO_LM => DATA_ADC0[119]) = (0:0:0, 0:0:0);
    (CLK_FIFO_LM => DATA_ADC0[11]) = (0:0:0, 0:0:0);
    (CLK_FIFO_LM => DATA_ADC0[120]) = (0:0:0, 0:0:0);
    (CLK_FIFO_LM => DATA_ADC0[121]) = (0:0:0, 0:0:0);
    (CLK_FIFO_LM => DATA_ADC0[122]) = (0:0:0, 0:0:0);
    (CLK_FIFO_LM => DATA_ADC0[123]) = (0:0:0, 0:0:0);
    (CLK_FIFO_LM => DATA_ADC0[124]) = (0:0:0, 0:0:0);
    (CLK_FIFO_LM => DATA_ADC0[125]) = (0:0:0, 0:0:0);
    (CLK_FIFO_LM => DATA_ADC0[126]) = (0:0:0, 0:0:0);
    (CLK_FIFO_LM => DATA_ADC0[127]) = (0:0:0, 0:0:0);
    (CLK_FIFO_LM => DATA_ADC0[128]) = (0:0:0, 0:0:0);
    (CLK_FIFO_LM => DATA_ADC0[129]) = (0:0:0, 0:0:0);
    (CLK_FIFO_LM => DATA_ADC0[12]) = (0:0:0, 0:0:0);
    (CLK_FIFO_LM => DATA_ADC0[130]) = (0:0:0, 0:0:0);
    (CLK_FIFO_LM => DATA_ADC0[131]) = (0:0:0, 0:0:0);
    (CLK_FIFO_LM => DATA_ADC0[132]) = (0:0:0, 0:0:0);
    (CLK_FIFO_LM => DATA_ADC0[133]) = (0:0:0, 0:0:0);
    (CLK_FIFO_LM => DATA_ADC0[134]) = (0:0:0, 0:0:0);
    (CLK_FIFO_LM => DATA_ADC0[135]) = (0:0:0, 0:0:0);
    (CLK_FIFO_LM => DATA_ADC0[136]) = (0:0:0, 0:0:0);
    (CLK_FIFO_LM => DATA_ADC0[137]) = (0:0:0, 0:0:0);
    (CLK_FIFO_LM => DATA_ADC0[138]) = (0:0:0, 0:0:0);
    (CLK_FIFO_LM => DATA_ADC0[139]) = (0:0:0, 0:0:0);
    (CLK_FIFO_LM => DATA_ADC0[13]) = (0:0:0, 0:0:0);
    (CLK_FIFO_LM => DATA_ADC0[140]) = (0:0:0, 0:0:0);
    (CLK_FIFO_LM => DATA_ADC0[141]) = (0:0:0, 0:0:0);
    (CLK_FIFO_LM => DATA_ADC0[142]) = (0:0:0, 0:0:0);
    (CLK_FIFO_LM => DATA_ADC0[143]) = (0:0:0, 0:0:0);
    (CLK_FIFO_LM => DATA_ADC0[144]) = (0:0:0, 0:0:0);
    (CLK_FIFO_LM => DATA_ADC0[145]) = (0:0:0, 0:0:0);
    (CLK_FIFO_LM => DATA_ADC0[146]) = (0:0:0, 0:0:0);
    (CLK_FIFO_LM => DATA_ADC0[147]) = (0:0:0, 0:0:0);
    (CLK_FIFO_LM => DATA_ADC0[148]) = (0:0:0, 0:0:0);
    (CLK_FIFO_LM => DATA_ADC0[149]) = (0:0:0, 0:0:0);
    (CLK_FIFO_LM => DATA_ADC0[14]) = (0:0:0, 0:0:0);
    (CLK_FIFO_LM => DATA_ADC0[150]) = (0:0:0, 0:0:0);
    (CLK_FIFO_LM => DATA_ADC0[151]) = (0:0:0, 0:0:0);
    (CLK_FIFO_LM => DATA_ADC0[152]) = (0:0:0, 0:0:0);
    (CLK_FIFO_LM => DATA_ADC0[153]) = (0:0:0, 0:0:0);
    (CLK_FIFO_LM => DATA_ADC0[154]) = (0:0:0, 0:0:0);
    (CLK_FIFO_LM => DATA_ADC0[155]) = (0:0:0, 0:0:0);
    (CLK_FIFO_LM => DATA_ADC0[156]) = (0:0:0, 0:0:0);
    (CLK_FIFO_LM => DATA_ADC0[157]) = (0:0:0, 0:0:0);
    (CLK_FIFO_LM => DATA_ADC0[158]) = (0:0:0, 0:0:0);
    (CLK_FIFO_LM => DATA_ADC0[159]) = (0:0:0, 0:0:0);
    (CLK_FIFO_LM => DATA_ADC0[15]) = (0:0:0, 0:0:0);
    (CLK_FIFO_LM => DATA_ADC0[160]) = (0:0:0, 0:0:0);
    (CLK_FIFO_LM => DATA_ADC0[161]) = (0:0:0, 0:0:0);
    (CLK_FIFO_LM => DATA_ADC0[162]) = (0:0:0, 0:0:0);
    (CLK_FIFO_LM => DATA_ADC0[163]) = (0:0:0, 0:0:0);
    (CLK_FIFO_LM => DATA_ADC0[164]) = (0:0:0, 0:0:0);
    (CLK_FIFO_LM => DATA_ADC0[165]) = (0:0:0, 0:0:0);
    (CLK_FIFO_LM => DATA_ADC0[166]) = (0:0:0, 0:0:0);
    (CLK_FIFO_LM => DATA_ADC0[167]) = (0:0:0, 0:0:0);
    (CLK_FIFO_LM => DATA_ADC0[168]) = (0:0:0, 0:0:0);
    (CLK_FIFO_LM => DATA_ADC0[169]) = (0:0:0, 0:0:0);
    (CLK_FIFO_LM => DATA_ADC0[16]) = (0:0:0, 0:0:0);
    (CLK_FIFO_LM => DATA_ADC0[170]) = (0:0:0, 0:0:0);
    (CLK_FIFO_LM => DATA_ADC0[171]) = (0:0:0, 0:0:0);
    (CLK_FIFO_LM => DATA_ADC0[172]) = (0:0:0, 0:0:0);
    (CLK_FIFO_LM => DATA_ADC0[173]) = (0:0:0, 0:0:0);
    (CLK_FIFO_LM => DATA_ADC0[174]) = (0:0:0, 0:0:0);
    (CLK_FIFO_LM => DATA_ADC0[175]) = (0:0:0, 0:0:0);
    (CLK_FIFO_LM => DATA_ADC0[176]) = (0:0:0, 0:0:0);
    (CLK_FIFO_LM => DATA_ADC0[177]) = (0:0:0, 0:0:0);
    (CLK_FIFO_LM => DATA_ADC0[178]) = (0:0:0, 0:0:0);
    (CLK_FIFO_LM => DATA_ADC0[179]) = (0:0:0, 0:0:0);
    (CLK_FIFO_LM => DATA_ADC0[17]) = (0:0:0, 0:0:0);
    (CLK_FIFO_LM => DATA_ADC0[180]) = (0:0:0, 0:0:0);
    (CLK_FIFO_LM => DATA_ADC0[181]) = (0:0:0, 0:0:0);
    (CLK_FIFO_LM => DATA_ADC0[182]) = (0:0:0, 0:0:0);
    (CLK_FIFO_LM => DATA_ADC0[183]) = (0:0:0, 0:0:0);
    (CLK_FIFO_LM => DATA_ADC0[184]) = (0:0:0, 0:0:0);
    (CLK_FIFO_LM => DATA_ADC0[185]) = (0:0:0, 0:0:0);
    (CLK_FIFO_LM => DATA_ADC0[186]) = (0:0:0, 0:0:0);
    (CLK_FIFO_LM => DATA_ADC0[187]) = (0:0:0, 0:0:0);
    (CLK_FIFO_LM => DATA_ADC0[188]) = (0:0:0, 0:0:0);
    (CLK_FIFO_LM => DATA_ADC0[189]) = (0:0:0, 0:0:0);
    (CLK_FIFO_LM => DATA_ADC0[18]) = (0:0:0, 0:0:0);
    (CLK_FIFO_LM => DATA_ADC0[190]) = (0:0:0, 0:0:0);
    (CLK_FIFO_LM => DATA_ADC0[191]) = (0:0:0, 0:0:0);
    (CLK_FIFO_LM => DATA_ADC0[19]) = (0:0:0, 0:0:0);
    (CLK_FIFO_LM => DATA_ADC0[1]) = (0:0:0, 0:0:0);
    (CLK_FIFO_LM => DATA_ADC0[20]) = (0:0:0, 0:0:0);
    (CLK_FIFO_LM => DATA_ADC0[21]) = (0:0:0, 0:0:0);
    (CLK_FIFO_LM => DATA_ADC0[22]) = (0:0:0, 0:0:0);
    (CLK_FIFO_LM => DATA_ADC0[23]) = (0:0:0, 0:0:0);
    (CLK_FIFO_LM => DATA_ADC0[24]) = (0:0:0, 0:0:0);
    (CLK_FIFO_LM => DATA_ADC0[25]) = (0:0:0, 0:0:0);
    (CLK_FIFO_LM => DATA_ADC0[26]) = (0:0:0, 0:0:0);
    (CLK_FIFO_LM => DATA_ADC0[27]) = (0:0:0, 0:0:0);
    (CLK_FIFO_LM => DATA_ADC0[28]) = (0:0:0, 0:0:0);
    (CLK_FIFO_LM => DATA_ADC0[29]) = (0:0:0, 0:0:0);
    (CLK_FIFO_LM => DATA_ADC0[2]) = (0:0:0, 0:0:0);
    (CLK_FIFO_LM => DATA_ADC0[30]) = (0:0:0, 0:0:0);
    (CLK_FIFO_LM => DATA_ADC0[31]) = (0:0:0, 0:0:0);
    (CLK_FIFO_LM => DATA_ADC0[32]) = (0:0:0, 0:0:0);
    (CLK_FIFO_LM => DATA_ADC0[33]) = (0:0:0, 0:0:0);
    (CLK_FIFO_LM => DATA_ADC0[34]) = (0:0:0, 0:0:0);
    (CLK_FIFO_LM => DATA_ADC0[35]) = (0:0:0, 0:0:0);
    (CLK_FIFO_LM => DATA_ADC0[36]) = (0:0:0, 0:0:0);
    (CLK_FIFO_LM => DATA_ADC0[37]) = (0:0:0, 0:0:0);
    (CLK_FIFO_LM => DATA_ADC0[38]) = (0:0:0, 0:0:0);
    (CLK_FIFO_LM => DATA_ADC0[39]) = (0:0:0, 0:0:0);
    (CLK_FIFO_LM => DATA_ADC0[3]) = (0:0:0, 0:0:0);
    (CLK_FIFO_LM => DATA_ADC0[40]) = (0:0:0, 0:0:0);
    (CLK_FIFO_LM => DATA_ADC0[41]) = (0:0:0, 0:0:0);
    (CLK_FIFO_LM => DATA_ADC0[42]) = (0:0:0, 0:0:0);
    (CLK_FIFO_LM => DATA_ADC0[43]) = (0:0:0, 0:0:0);
    (CLK_FIFO_LM => DATA_ADC0[44]) = (0:0:0, 0:0:0);
    (CLK_FIFO_LM => DATA_ADC0[45]) = (0:0:0, 0:0:0);
    (CLK_FIFO_LM => DATA_ADC0[46]) = (0:0:0, 0:0:0);
    (CLK_FIFO_LM => DATA_ADC0[47]) = (0:0:0, 0:0:0);
    (CLK_FIFO_LM => DATA_ADC0[48]) = (0:0:0, 0:0:0);
    (CLK_FIFO_LM => DATA_ADC0[49]) = (0:0:0, 0:0:0);
    (CLK_FIFO_LM => DATA_ADC0[4]) = (0:0:0, 0:0:0);
    (CLK_FIFO_LM => DATA_ADC0[50]) = (0:0:0, 0:0:0);
    (CLK_FIFO_LM => DATA_ADC0[51]) = (0:0:0, 0:0:0);
    (CLK_FIFO_LM => DATA_ADC0[52]) = (0:0:0, 0:0:0);
    (CLK_FIFO_LM => DATA_ADC0[53]) = (0:0:0, 0:0:0);
    (CLK_FIFO_LM => DATA_ADC0[54]) = (0:0:0, 0:0:0);
    (CLK_FIFO_LM => DATA_ADC0[55]) = (0:0:0, 0:0:0);
    (CLK_FIFO_LM => DATA_ADC0[56]) = (0:0:0, 0:0:0);
    (CLK_FIFO_LM => DATA_ADC0[57]) = (0:0:0, 0:0:0);
    (CLK_FIFO_LM => DATA_ADC0[58]) = (0:0:0, 0:0:0);
    (CLK_FIFO_LM => DATA_ADC0[59]) = (0:0:0, 0:0:0);
    (CLK_FIFO_LM => DATA_ADC0[5]) = (0:0:0, 0:0:0);
    (CLK_FIFO_LM => DATA_ADC0[60]) = (0:0:0, 0:0:0);
    (CLK_FIFO_LM => DATA_ADC0[61]) = (0:0:0, 0:0:0);
    (CLK_FIFO_LM => DATA_ADC0[62]) = (0:0:0, 0:0:0);
    (CLK_FIFO_LM => DATA_ADC0[63]) = (0:0:0, 0:0:0);
    (CLK_FIFO_LM => DATA_ADC0[64]) = (0:0:0, 0:0:0);
    (CLK_FIFO_LM => DATA_ADC0[65]) = (0:0:0, 0:0:0);
    (CLK_FIFO_LM => DATA_ADC0[66]) = (0:0:0, 0:0:0);
    (CLK_FIFO_LM => DATA_ADC0[67]) = (0:0:0, 0:0:0);
    (CLK_FIFO_LM => DATA_ADC0[68]) = (0:0:0, 0:0:0);
    (CLK_FIFO_LM => DATA_ADC0[69]) = (0:0:0, 0:0:0);
    (CLK_FIFO_LM => DATA_ADC0[6]) = (0:0:0, 0:0:0);
    (CLK_FIFO_LM => DATA_ADC0[70]) = (0:0:0, 0:0:0);
    (CLK_FIFO_LM => DATA_ADC0[71]) = (0:0:0, 0:0:0);
    (CLK_FIFO_LM => DATA_ADC0[72]) = (0:0:0, 0:0:0);
    (CLK_FIFO_LM => DATA_ADC0[73]) = (0:0:0, 0:0:0);
    (CLK_FIFO_LM => DATA_ADC0[74]) = (0:0:0, 0:0:0);
    (CLK_FIFO_LM => DATA_ADC0[75]) = (0:0:0, 0:0:0);
    (CLK_FIFO_LM => DATA_ADC0[76]) = (0:0:0, 0:0:0);
    (CLK_FIFO_LM => DATA_ADC0[77]) = (0:0:0, 0:0:0);
    (CLK_FIFO_LM => DATA_ADC0[78]) = (0:0:0, 0:0:0);
    (CLK_FIFO_LM => DATA_ADC0[79]) = (0:0:0, 0:0:0);
    (CLK_FIFO_LM => DATA_ADC0[7]) = (0:0:0, 0:0:0);
    (CLK_FIFO_LM => DATA_ADC0[80]) = (0:0:0, 0:0:0);
    (CLK_FIFO_LM => DATA_ADC0[81]) = (0:0:0, 0:0:0);
    (CLK_FIFO_LM => DATA_ADC0[82]) = (0:0:0, 0:0:0);
    (CLK_FIFO_LM => DATA_ADC0[83]) = (0:0:0, 0:0:0);
    (CLK_FIFO_LM => DATA_ADC0[84]) = (0:0:0, 0:0:0);
    (CLK_FIFO_LM => DATA_ADC0[85]) = (0:0:0, 0:0:0);
    (CLK_FIFO_LM => DATA_ADC0[86]) = (0:0:0, 0:0:0);
    (CLK_FIFO_LM => DATA_ADC0[87]) = (0:0:0, 0:0:0);
    (CLK_FIFO_LM => DATA_ADC0[88]) = (0:0:0, 0:0:0);
    (CLK_FIFO_LM => DATA_ADC0[89]) = (0:0:0, 0:0:0);
    (CLK_FIFO_LM => DATA_ADC0[8]) = (0:0:0, 0:0:0);
    (CLK_FIFO_LM => DATA_ADC0[90]) = (0:0:0, 0:0:0);
    (CLK_FIFO_LM => DATA_ADC0[91]) = (0:0:0, 0:0:0);
    (CLK_FIFO_LM => DATA_ADC0[92]) = (0:0:0, 0:0:0);
    (CLK_FIFO_LM => DATA_ADC0[93]) = (0:0:0, 0:0:0);
    (CLK_FIFO_LM => DATA_ADC0[94]) = (0:0:0, 0:0:0);
    (CLK_FIFO_LM => DATA_ADC0[95]) = (0:0:0, 0:0:0);
    (CLK_FIFO_LM => DATA_ADC0[96]) = (0:0:0, 0:0:0);
    (CLK_FIFO_LM => DATA_ADC0[97]) = (0:0:0, 0:0:0);
    (CLK_FIFO_LM => DATA_ADC0[98]) = (0:0:0, 0:0:0);
    (CLK_FIFO_LM => DATA_ADC0[99]) = (0:0:0, 0:0:0);
    (CLK_FIFO_LM => DATA_ADC0[9]) = (0:0:0, 0:0:0);
    (CLK_FIFO_LM => DATA_ADC1[0]) = (0:0:0, 0:0:0);
    (CLK_FIFO_LM => DATA_ADC1[100]) = (0:0:0, 0:0:0);
    (CLK_FIFO_LM => DATA_ADC1[101]) = (0:0:0, 0:0:0);
    (CLK_FIFO_LM => DATA_ADC1[102]) = (0:0:0, 0:0:0);
    (CLK_FIFO_LM => DATA_ADC1[103]) = (0:0:0, 0:0:0);
    (CLK_FIFO_LM => DATA_ADC1[104]) = (0:0:0, 0:0:0);
    (CLK_FIFO_LM => DATA_ADC1[105]) = (0:0:0, 0:0:0);
    (CLK_FIFO_LM => DATA_ADC1[106]) = (0:0:0, 0:0:0);
    (CLK_FIFO_LM => DATA_ADC1[107]) = (0:0:0, 0:0:0);
    (CLK_FIFO_LM => DATA_ADC1[108]) = (0:0:0, 0:0:0);
    (CLK_FIFO_LM => DATA_ADC1[109]) = (0:0:0, 0:0:0);
    (CLK_FIFO_LM => DATA_ADC1[10]) = (0:0:0, 0:0:0);
    (CLK_FIFO_LM => DATA_ADC1[110]) = (0:0:0, 0:0:0);
    (CLK_FIFO_LM => DATA_ADC1[111]) = (0:0:0, 0:0:0);
    (CLK_FIFO_LM => DATA_ADC1[112]) = (0:0:0, 0:0:0);
    (CLK_FIFO_LM => DATA_ADC1[113]) = (0:0:0, 0:0:0);
    (CLK_FIFO_LM => DATA_ADC1[114]) = (0:0:0, 0:0:0);
    (CLK_FIFO_LM => DATA_ADC1[115]) = (0:0:0, 0:0:0);
    (CLK_FIFO_LM => DATA_ADC1[116]) = (0:0:0, 0:0:0);
    (CLK_FIFO_LM => DATA_ADC1[117]) = (0:0:0, 0:0:0);
    (CLK_FIFO_LM => DATA_ADC1[118]) = (0:0:0, 0:0:0);
    (CLK_FIFO_LM => DATA_ADC1[119]) = (0:0:0, 0:0:0);
    (CLK_FIFO_LM => DATA_ADC1[11]) = (0:0:0, 0:0:0);
    (CLK_FIFO_LM => DATA_ADC1[120]) = (0:0:0, 0:0:0);
    (CLK_FIFO_LM => DATA_ADC1[121]) = (0:0:0, 0:0:0);
    (CLK_FIFO_LM => DATA_ADC1[122]) = (0:0:0, 0:0:0);
    (CLK_FIFO_LM => DATA_ADC1[123]) = (0:0:0, 0:0:0);
    (CLK_FIFO_LM => DATA_ADC1[124]) = (0:0:0, 0:0:0);
    (CLK_FIFO_LM => DATA_ADC1[125]) = (0:0:0, 0:0:0);
    (CLK_FIFO_LM => DATA_ADC1[126]) = (0:0:0, 0:0:0);
    (CLK_FIFO_LM => DATA_ADC1[127]) = (0:0:0, 0:0:0);
    (CLK_FIFO_LM => DATA_ADC1[128]) = (0:0:0, 0:0:0);
    (CLK_FIFO_LM => DATA_ADC1[129]) = (0:0:0, 0:0:0);
    (CLK_FIFO_LM => DATA_ADC1[12]) = (0:0:0, 0:0:0);
    (CLK_FIFO_LM => DATA_ADC1[130]) = (0:0:0, 0:0:0);
    (CLK_FIFO_LM => DATA_ADC1[131]) = (0:0:0, 0:0:0);
    (CLK_FIFO_LM => DATA_ADC1[132]) = (0:0:0, 0:0:0);
    (CLK_FIFO_LM => DATA_ADC1[133]) = (0:0:0, 0:0:0);
    (CLK_FIFO_LM => DATA_ADC1[134]) = (0:0:0, 0:0:0);
    (CLK_FIFO_LM => DATA_ADC1[135]) = (0:0:0, 0:0:0);
    (CLK_FIFO_LM => DATA_ADC1[136]) = (0:0:0, 0:0:0);
    (CLK_FIFO_LM => DATA_ADC1[137]) = (0:0:0, 0:0:0);
    (CLK_FIFO_LM => DATA_ADC1[138]) = (0:0:0, 0:0:0);
    (CLK_FIFO_LM => DATA_ADC1[139]) = (0:0:0, 0:0:0);
    (CLK_FIFO_LM => DATA_ADC1[13]) = (0:0:0, 0:0:0);
    (CLK_FIFO_LM => DATA_ADC1[140]) = (0:0:0, 0:0:0);
    (CLK_FIFO_LM => DATA_ADC1[141]) = (0:0:0, 0:0:0);
    (CLK_FIFO_LM => DATA_ADC1[142]) = (0:0:0, 0:0:0);
    (CLK_FIFO_LM => DATA_ADC1[143]) = (0:0:0, 0:0:0);
    (CLK_FIFO_LM => DATA_ADC1[144]) = (0:0:0, 0:0:0);
    (CLK_FIFO_LM => DATA_ADC1[145]) = (0:0:0, 0:0:0);
    (CLK_FIFO_LM => DATA_ADC1[146]) = (0:0:0, 0:0:0);
    (CLK_FIFO_LM => DATA_ADC1[147]) = (0:0:0, 0:0:0);
    (CLK_FIFO_LM => DATA_ADC1[148]) = (0:0:0, 0:0:0);
    (CLK_FIFO_LM => DATA_ADC1[149]) = (0:0:0, 0:0:0);
    (CLK_FIFO_LM => DATA_ADC1[14]) = (0:0:0, 0:0:0);
    (CLK_FIFO_LM => DATA_ADC1[150]) = (0:0:0, 0:0:0);
    (CLK_FIFO_LM => DATA_ADC1[151]) = (0:0:0, 0:0:0);
    (CLK_FIFO_LM => DATA_ADC1[152]) = (0:0:0, 0:0:0);
    (CLK_FIFO_LM => DATA_ADC1[153]) = (0:0:0, 0:0:0);
    (CLK_FIFO_LM => DATA_ADC1[154]) = (0:0:0, 0:0:0);
    (CLK_FIFO_LM => DATA_ADC1[155]) = (0:0:0, 0:0:0);
    (CLK_FIFO_LM => DATA_ADC1[156]) = (0:0:0, 0:0:0);
    (CLK_FIFO_LM => DATA_ADC1[157]) = (0:0:0, 0:0:0);
    (CLK_FIFO_LM => DATA_ADC1[158]) = (0:0:0, 0:0:0);
    (CLK_FIFO_LM => DATA_ADC1[159]) = (0:0:0, 0:0:0);
    (CLK_FIFO_LM => DATA_ADC1[15]) = (0:0:0, 0:0:0);
    (CLK_FIFO_LM => DATA_ADC1[160]) = (0:0:0, 0:0:0);
    (CLK_FIFO_LM => DATA_ADC1[161]) = (0:0:0, 0:0:0);
    (CLK_FIFO_LM => DATA_ADC1[162]) = (0:0:0, 0:0:0);
    (CLK_FIFO_LM => DATA_ADC1[163]) = (0:0:0, 0:0:0);
    (CLK_FIFO_LM => DATA_ADC1[164]) = (0:0:0, 0:0:0);
    (CLK_FIFO_LM => DATA_ADC1[165]) = (0:0:0, 0:0:0);
    (CLK_FIFO_LM => DATA_ADC1[166]) = (0:0:0, 0:0:0);
    (CLK_FIFO_LM => DATA_ADC1[167]) = (0:0:0, 0:0:0);
    (CLK_FIFO_LM => DATA_ADC1[168]) = (0:0:0, 0:0:0);
    (CLK_FIFO_LM => DATA_ADC1[169]) = (0:0:0, 0:0:0);
    (CLK_FIFO_LM => DATA_ADC1[16]) = (0:0:0, 0:0:0);
    (CLK_FIFO_LM => DATA_ADC1[170]) = (0:0:0, 0:0:0);
    (CLK_FIFO_LM => DATA_ADC1[171]) = (0:0:0, 0:0:0);
    (CLK_FIFO_LM => DATA_ADC1[172]) = (0:0:0, 0:0:0);
    (CLK_FIFO_LM => DATA_ADC1[173]) = (0:0:0, 0:0:0);
    (CLK_FIFO_LM => DATA_ADC1[174]) = (0:0:0, 0:0:0);
    (CLK_FIFO_LM => DATA_ADC1[175]) = (0:0:0, 0:0:0);
    (CLK_FIFO_LM => DATA_ADC1[176]) = (0:0:0, 0:0:0);
    (CLK_FIFO_LM => DATA_ADC1[177]) = (0:0:0, 0:0:0);
    (CLK_FIFO_LM => DATA_ADC1[178]) = (0:0:0, 0:0:0);
    (CLK_FIFO_LM => DATA_ADC1[179]) = (0:0:0, 0:0:0);
    (CLK_FIFO_LM => DATA_ADC1[17]) = (0:0:0, 0:0:0);
    (CLK_FIFO_LM => DATA_ADC1[180]) = (0:0:0, 0:0:0);
    (CLK_FIFO_LM => DATA_ADC1[181]) = (0:0:0, 0:0:0);
    (CLK_FIFO_LM => DATA_ADC1[182]) = (0:0:0, 0:0:0);
    (CLK_FIFO_LM => DATA_ADC1[183]) = (0:0:0, 0:0:0);
    (CLK_FIFO_LM => DATA_ADC1[184]) = (0:0:0, 0:0:0);
    (CLK_FIFO_LM => DATA_ADC1[185]) = (0:0:0, 0:0:0);
    (CLK_FIFO_LM => DATA_ADC1[186]) = (0:0:0, 0:0:0);
    (CLK_FIFO_LM => DATA_ADC1[187]) = (0:0:0, 0:0:0);
    (CLK_FIFO_LM => DATA_ADC1[188]) = (0:0:0, 0:0:0);
    (CLK_FIFO_LM => DATA_ADC1[189]) = (0:0:0, 0:0:0);
    (CLK_FIFO_LM => DATA_ADC1[18]) = (0:0:0, 0:0:0);
    (CLK_FIFO_LM => DATA_ADC1[190]) = (0:0:0, 0:0:0);
    (CLK_FIFO_LM => DATA_ADC1[191]) = (0:0:0, 0:0:0);
    (CLK_FIFO_LM => DATA_ADC1[19]) = (0:0:0, 0:0:0);
    (CLK_FIFO_LM => DATA_ADC1[1]) = (0:0:0, 0:0:0);
    (CLK_FIFO_LM => DATA_ADC1[20]) = (0:0:0, 0:0:0);
    (CLK_FIFO_LM => DATA_ADC1[21]) = (0:0:0, 0:0:0);
    (CLK_FIFO_LM => DATA_ADC1[22]) = (0:0:0, 0:0:0);
    (CLK_FIFO_LM => DATA_ADC1[23]) = (0:0:0, 0:0:0);
    (CLK_FIFO_LM => DATA_ADC1[24]) = (0:0:0, 0:0:0);
    (CLK_FIFO_LM => DATA_ADC1[25]) = (0:0:0, 0:0:0);
    (CLK_FIFO_LM => DATA_ADC1[26]) = (0:0:0, 0:0:0);
    (CLK_FIFO_LM => DATA_ADC1[27]) = (0:0:0, 0:0:0);
    (CLK_FIFO_LM => DATA_ADC1[28]) = (0:0:0, 0:0:0);
    (CLK_FIFO_LM => DATA_ADC1[29]) = (0:0:0, 0:0:0);
    (CLK_FIFO_LM => DATA_ADC1[2]) = (0:0:0, 0:0:0);
    (CLK_FIFO_LM => DATA_ADC1[30]) = (0:0:0, 0:0:0);
    (CLK_FIFO_LM => DATA_ADC1[31]) = (0:0:0, 0:0:0);
    (CLK_FIFO_LM => DATA_ADC1[32]) = (0:0:0, 0:0:0);
    (CLK_FIFO_LM => DATA_ADC1[33]) = (0:0:0, 0:0:0);
    (CLK_FIFO_LM => DATA_ADC1[34]) = (0:0:0, 0:0:0);
    (CLK_FIFO_LM => DATA_ADC1[35]) = (0:0:0, 0:0:0);
    (CLK_FIFO_LM => DATA_ADC1[36]) = (0:0:0, 0:0:0);
    (CLK_FIFO_LM => DATA_ADC1[37]) = (0:0:0, 0:0:0);
    (CLK_FIFO_LM => DATA_ADC1[38]) = (0:0:0, 0:0:0);
    (CLK_FIFO_LM => DATA_ADC1[39]) = (0:0:0, 0:0:0);
    (CLK_FIFO_LM => DATA_ADC1[3]) = (0:0:0, 0:0:0);
    (CLK_FIFO_LM => DATA_ADC1[40]) = (0:0:0, 0:0:0);
    (CLK_FIFO_LM => DATA_ADC1[41]) = (0:0:0, 0:0:0);
    (CLK_FIFO_LM => DATA_ADC1[42]) = (0:0:0, 0:0:0);
    (CLK_FIFO_LM => DATA_ADC1[43]) = (0:0:0, 0:0:0);
    (CLK_FIFO_LM => DATA_ADC1[44]) = (0:0:0, 0:0:0);
    (CLK_FIFO_LM => DATA_ADC1[45]) = (0:0:0, 0:0:0);
    (CLK_FIFO_LM => DATA_ADC1[46]) = (0:0:0, 0:0:0);
    (CLK_FIFO_LM => DATA_ADC1[47]) = (0:0:0, 0:0:0);
    (CLK_FIFO_LM => DATA_ADC1[48]) = (0:0:0, 0:0:0);
    (CLK_FIFO_LM => DATA_ADC1[49]) = (0:0:0, 0:0:0);
    (CLK_FIFO_LM => DATA_ADC1[4]) = (0:0:0, 0:0:0);
    (CLK_FIFO_LM => DATA_ADC1[50]) = (0:0:0, 0:0:0);
    (CLK_FIFO_LM => DATA_ADC1[51]) = (0:0:0, 0:0:0);
    (CLK_FIFO_LM => DATA_ADC1[52]) = (0:0:0, 0:0:0);
    (CLK_FIFO_LM => DATA_ADC1[53]) = (0:0:0, 0:0:0);
    (CLK_FIFO_LM => DATA_ADC1[54]) = (0:0:0, 0:0:0);
    (CLK_FIFO_LM => DATA_ADC1[55]) = (0:0:0, 0:0:0);
    (CLK_FIFO_LM => DATA_ADC1[56]) = (0:0:0, 0:0:0);
    (CLK_FIFO_LM => DATA_ADC1[57]) = (0:0:0, 0:0:0);
    (CLK_FIFO_LM => DATA_ADC1[58]) = (0:0:0, 0:0:0);
    (CLK_FIFO_LM => DATA_ADC1[59]) = (0:0:0, 0:0:0);
    (CLK_FIFO_LM => DATA_ADC1[5]) = (0:0:0, 0:0:0);
    (CLK_FIFO_LM => DATA_ADC1[60]) = (0:0:0, 0:0:0);
    (CLK_FIFO_LM => DATA_ADC1[61]) = (0:0:0, 0:0:0);
    (CLK_FIFO_LM => DATA_ADC1[62]) = (0:0:0, 0:0:0);
    (CLK_FIFO_LM => DATA_ADC1[63]) = (0:0:0, 0:0:0);
    (CLK_FIFO_LM => DATA_ADC1[64]) = (0:0:0, 0:0:0);
    (CLK_FIFO_LM => DATA_ADC1[65]) = (0:0:0, 0:0:0);
    (CLK_FIFO_LM => DATA_ADC1[66]) = (0:0:0, 0:0:0);
    (CLK_FIFO_LM => DATA_ADC1[67]) = (0:0:0, 0:0:0);
    (CLK_FIFO_LM => DATA_ADC1[68]) = (0:0:0, 0:0:0);
    (CLK_FIFO_LM => DATA_ADC1[69]) = (0:0:0, 0:0:0);
    (CLK_FIFO_LM => DATA_ADC1[6]) = (0:0:0, 0:0:0);
    (CLK_FIFO_LM => DATA_ADC1[70]) = (0:0:0, 0:0:0);
    (CLK_FIFO_LM => DATA_ADC1[71]) = (0:0:0, 0:0:0);
    (CLK_FIFO_LM => DATA_ADC1[72]) = (0:0:0, 0:0:0);
    (CLK_FIFO_LM => DATA_ADC1[73]) = (0:0:0, 0:0:0);
    (CLK_FIFO_LM => DATA_ADC1[74]) = (0:0:0, 0:0:0);
    (CLK_FIFO_LM => DATA_ADC1[75]) = (0:0:0, 0:0:0);
    (CLK_FIFO_LM => DATA_ADC1[76]) = (0:0:0, 0:0:0);
    (CLK_FIFO_LM => DATA_ADC1[77]) = (0:0:0, 0:0:0);
    (CLK_FIFO_LM => DATA_ADC1[78]) = (0:0:0, 0:0:0);
    (CLK_FIFO_LM => DATA_ADC1[79]) = (0:0:0, 0:0:0);
    (CLK_FIFO_LM => DATA_ADC1[7]) = (0:0:0, 0:0:0);
    (CLK_FIFO_LM => DATA_ADC1[80]) = (0:0:0, 0:0:0);
    (CLK_FIFO_LM => DATA_ADC1[81]) = (0:0:0, 0:0:0);
    (CLK_FIFO_LM => DATA_ADC1[82]) = (0:0:0, 0:0:0);
    (CLK_FIFO_LM => DATA_ADC1[83]) = (0:0:0, 0:0:0);
    (CLK_FIFO_LM => DATA_ADC1[84]) = (0:0:0, 0:0:0);
    (CLK_FIFO_LM => DATA_ADC1[85]) = (0:0:0, 0:0:0);
    (CLK_FIFO_LM => DATA_ADC1[86]) = (0:0:0, 0:0:0);
    (CLK_FIFO_LM => DATA_ADC1[87]) = (0:0:0, 0:0:0);
    (CLK_FIFO_LM => DATA_ADC1[88]) = (0:0:0, 0:0:0);
    (CLK_FIFO_LM => DATA_ADC1[89]) = (0:0:0, 0:0:0);
    (CLK_FIFO_LM => DATA_ADC1[8]) = (0:0:0, 0:0:0);
    (CLK_FIFO_LM => DATA_ADC1[90]) = (0:0:0, 0:0:0);
    (CLK_FIFO_LM => DATA_ADC1[91]) = (0:0:0, 0:0:0);
    (CLK_FIFO_LM => DATA_ADC1[92]) = (0:0:0, 0:0:0);
    (CLK_FIFO_LM => DATA_ADC1[93]) = (0:0:0, 0:0:0);
    (CLK_FIFO_LM => DATA_ADC1[94]) = (0:0:0, 0:0:0);
    (CLK_FIFO_LM => DATA_ADC1[95]) = (0:0:0, 0:0:0);
    (CLK_FIFO_LM => DATA_ADC1[96]) = (0:0:0, 0:0:0);
    (CLK_FIFO_LM => DATA_ADC1[97]) = (0:0:0, 0:0:0);
    (CLK_FIFO_LM => DATA_ADC1[98]) = (0:0:0, 0:0:0);
    (CLK_FIFO_LM => DATA_ADC1[99]) = (0:0:0, 0:0:0);
    (CLK_FIFO_LM => DATA_ADC1[9]) = (0:0:0, 0:0:0);
    (CLK_FIFO_LM => DATA_ADC2[0]) = (0:0:0, 0:0:0);
    (CLK_FIFO_LM => DATA_ADC2[100]) = (0:0:0, 0:0:0);
    (CLK_FIFO_LM => DATA_ADC2[101]) = (0:0:0, 0:0:0);
    (CLK_FIFO_LM => DATA_ADC2[102]) = (0:0:0, 0:0:0);
    (CLK_FIFO_LM => DATA_ADC2[103]) = (0:0:0, 0:0:0);
    (CLK_FIFO_LM => DATA_ADC2[104]) = (0:0:0, 0:0:0);
    (CLK_FIFO_LM => DATA_ADC2[105]) = (0:0:0, 0:0:0);
    (CLK_FIFO_LM => DATA_ADC2[106]) = (0:0:0, 0:0:0);
    (CLK_FIFO_LM => DATA_ADC2[107]) = (0:0:0, 0:0:0);
    (CLK_FIFO_LM => DATA_ADC2[108]) = (0:0:0, 0:0:0);
    (CLK_FIFO_LM => DATA_ADC2[109]) = (0:0:0, 0:0:0);
    (CLK_FIFO_LM => DATA_ADC2[10]) = (0:0:0, 0:0:0);
    (CLK_FIFO_LM => DATA_ADC2[110]) = (0:0:0, 0:0:0);
    (CLK_FIFO_LM => DATA_ADC2[111]) = (0:0:0, 0:0:0);
    (CLK_FIFO_LM => DATA_ADC2[112]) = (0:0:0, 0:0:0);
    (CLK_FIFO_LM => DATA_ADC2[113]) = (0:0:0, 0:0:0);
    (CLK_FIFO_LM => DATA_ADC2[114]) = (0:0:0, 0:0:0);
    (CLK_FIFO_LM => DATA_ADC2[115]) = (0:0:0, 0:0:0);
    (CLK_FIFO_LM => DATA_ADC2[116]) = (0:0:0, 0:0:0);
    (CLK_FIFO_LM => DATA_ADC2[117]) = (0:0:0, 0:0:0);
    (CLK_FIFO_LM => DATA_ADC2[118]) = (0:0:0, 0:0:0);
    (CLK_FIFO_LM => DATA_ADC2[119]) = (0:0:0, 0:0:0);
    (CLK_FIFO_LM => DATA_ADC2[11]) = (0:0:0, 0:0:0);
    (CLK_FIFO_LM => DATA_ADC2[120]) = (0:0:0, 0:0:0);
    (CLK_FIFO_LM => DATA_ADC2[121]) = (0:0:0, 0:0:0);
    (CLK_FIFO_LM => DATA_ADC2[122]) = (0:0:0, 0:0:0);
    (CLK_FIFO_LM => DATA_ADC2[123]) = (0:0:0, 0:0:0);
    (CLK_FIFO_LM => DATA_ADC2[124]) = (0:0:0, 0:0:0);
    (CLK_FIFO_LM => DATA_ADC2[125]) = (0:0:0, 0:0:0);
    (CLK_FIFO_LM => DATA_ADC2[126]) = (0:0:0, 0:0:0);
    (CLK_FIFO_LM => DATA_ADC2[127]) = (0:0:0, 0:0:0);
    (CLK_FIFO_LM => DATA_ADC2[128]) = (0:0:0, 0:0:0);
    (CLK_FIFO_LM => DATA_ADC2[129]) = (0:0:0, 0:0:0);
    (CLK_FIFO_LM => DATA_ADC2[12]) = (0:0:0, 0:0:0);
    (CLK_FIFO_LM => DATA_ADC2[130]) = (0:0:0, 0:0:0);
    (CLK_FIFO_LM => DATA_ADC2[131]) = (0:0:0, 0:0:0);
    (CLK_FIFO_LM => DATA_ADC2[132]) = (0:0:0, 0:0:0);
    (CLK_FIFO_LM => DATA_ADC2[133]) = (0:0:0, 0:0:0);
    (CLK_FIFO_LM => DATA_ADC2[134]) = (0:0:0, 0:0:0);
    (CLK_FIFO_LM => DATA_ADC2[135]) = (0:0:0, 0:0:0);
    (CLK_FIFO_LM => DATA_ADC2[136]) = (0:0:0, 0:0:0);
    (CLK_FIFO_LM => DATA_ADC2[137]) = (0:0:0, 0:0:0);
    (CLK_FIFO_LM => DATA_ADC2[138]) = (0:0:0, 0:0:0);
    (CLK_FIFO_LM => DATA_ADC2[139]) = (0:0:0, 0:0:0);
    (CLK_FIFO_LM => DATA_ADC2[13]) = (0:0:0, 0:0:0);
    (CLK_FIFO_LM => DATA_ADC2[140]) = (0:0:0, 0:0:0);
    (CLK_FIFO_LM => DATA_ADC2[141]) = (0:0:0, 0:0:0);
    (CLK_FIFO_LM => DATA_ADC2[142]) = (0:0:0, 0:0:0);
    (CLK_FIFO_LM => DATA_ADC2[143]) = (0:0:0, 0:0:0);
    (CLK_FIFO_LM => DATA_ADC2[144]) = (0:0:0, 0:0:0);
    (CLK_FIFO_LM => DATA_ADC2[145]) = (0:0:0, 0:0:0);
    (CLK_FIFO_LM => DATA_ADC2[146]) = (0:0:0, 0:0:0);
    (CLK_FIFO_LM => DATA_ADC2[147]) = (0:0:0, 0:0:0);
    (CLK_FIFO_LM => DATA_ADC2[148]) = (0:0:0, 0:0:0);
    (CLK_FIFO_LM => DATA_ADC2[149]) = (0:0:0, 0:0:0);
    (CLK_FIFO_LM => DATA_ADC2[14]) = (0:0:0, 0:0:0);
    (CLK_FIFO_LM => DATA_ADC2[150]) = (0:0:0, 0:0:0);
    (CLK_FIFO_LM => DATA_ADC2[151]) = (0:0:0, 0:0:0);
    (CLK_FIFO_LM => DATA_ADC2[152]) = (0:0:0, 0:0:0);
    (CLK_FIFO_LM => DATA_ADC2[153]) = (0:0:0, 0:0:0);
    (CLK_FIFO_LM => DATA_ADC2[154]) = (0:0:0, 0:0:0);
    (CLK_FIFO_LM => DATA_ADC2[155]) = (0:0:0, 0:0:0);
    (CLK_FIFO_LM => DATA_ADC2[156]) = (0:0:0, 0:0:0);
    (CLK_FIFO_LM => DATA_ADC2[157]) = (0:0:0, 0:0:0);
    (CLK_FIFO_LM => DATA_ADC2[158]) = (0:0:0, 0:0:0);
    (CLK_FIFO_LM => DATA_ADC2[159]) = (0:0:0, 0:0:0);
    (CLK_FIFO_LM => DATA_ADC2[15]) = (0:0:0, 0:0:0);
    (CLK_FIFO_LM => DATA_ADC2[160]) = (0:0:0, 0:0:0);
    (CLK_FIFO_LM => DATA_ADC2[161]) = (0:0:0, 0:0:0);
    (CLK_FIFO_LM => DATA_ADC2[162]) = (0:0:0, 0:0:0);
    (CLK_FIFO_LM => DATA_ADC2[163]) = (0:0:0, 0:0:0);
    (CLK_FIFO_LM => DATA_ADC2[164]) = (0:0:0, 0:0:0);
    (CLK_FIFO_LM => DATA_ADC2[165]) = (0:0:0, 0:0:0);
    (CLK_FIFO_LM => DATA_ADC2[166]) = (0:0:0, 0:0:0);
    (CLK_FIFO_LM => DATA_ADC2[167]) = (0:0:0, 0:0:0);
    (CLK_FIFO_LM => DATA_ADC2[168]) = (0:0:0, 0:0:0);
    (CLK_FIFO_LM => DATA_ADC2[169]) = (0:0:0, 0:0:0);
    (CLK_FIFO_LM => DATA_ADC2[16]) = (0:0:0, 0:0:0);
    (CLK_FIFO_LM => DATA_ADC2[170]) = (0:0:0, 0:0:0);
    (CLK_FIFO_LM => DATA_ADC2[171]) = (0:0:0, 0:0:0);
    (CLK_FIFO_LM => DATA_ADC2[172]) = (0:0:0, 0:0:0);
    (CLK_FIFO_LM => DATA_ADC2[173]) = (0:0:0, 0:0:0);
    (CLK_FIFO_LM => DATA_ADC2[174]) = (0:0:0, 0:0:0);
    (CLK_FIFO_LM => DATA_ADC2[175]) = (0:0:0, 0:0:0);
    (CLK_FIFO_LM => DATA_ADC2[176]) = (0:0:0, 0:0:0);
    (CLK_FIFO_LM => DATA_ADC2[177]) = (0:0:0, 0:0:0);
    (CLK_FIFO_LM => DATA_ADC2[178]) = (0:0:0, 0:0:0);
    (CLK_FIFO_LM => DATA_ADC2[179]) = (0:0:0, 0:0:0);
    (CLK_FIFO_LM => DATA_ADC2[17]) = (0:0:0, 0:0:0);
    (CLK_FIFO_LM => DATA_ADC2[180]) = (0:0:0, 0:0:0);
    (CLK_FIFO_LM => DATA_ADC2[181]) = (0:0:0, 0:0:0);
    (CLK_FIFO_LM => DATA_ADC2[182]) = (0:0:0, 0:0:0);
    (CLK_FIFO_LM => DATA_ADC2[183]) = (0:0:0, 0:0:0);
    (CLK_FIFO_LM => DATA_ADC2[184]) = (0:0:0, 0:0:0);
    (CLK_FIFO_LM => DATA_ADC2[185]) = (0:0:0, 0:0:0);
    (CLK_FIFO_LM => DATA_ADC2[186]) = (0:0:0, 0:0:0);
    (CLK_FIFO_LM => DATA_ADC2[187]) = (0:0:0, 0:0:0);
    (CLK_FIFO_LM => DATA_ADC2[188]) = (0:0:0, 0:0:0);
    (CLK_FIFO_LM => DATA_ADC2[189]) = (0:0:0, 0:0:0);
    (CLK_FIFO_LM => DATA_ADC2[18]) = (0:0:0, 0:0:0);
    (CLK_FIFO_LM => DATA_ADC2[190]) = (0:0:0, 0:0:0);
    (CLK_FIFO_LM => DATA_ADC2[191]) = (0:0:0, 0:0:0);
    (CLK_FIFO_LM => DATA_ADC2[19]) = (0:0:0, 0:0:0);
    (CLK_FIFO_LM => DATA_ADC2[1]) = (0:0:0, 0:0:0);
    (CLK_FIFO_LM => DATA_ADC2[20]) = (0:0:0, 0:0:0);
    (CLK_FIFO_LM => DATA_ADC2[21]) = (0:0:0, 0:0:0);
    (CLK_FIFO_LM => DATA_ADC2[22]) = (0:0:0, 0:0:0);
    (CLK_FIFO_LM => DATA_ADC2[23]) = (0:0:0, 0:0:0);
    (CLK_FIFO_LM => DATA_ADC2[24]) = (0:0:0, 0:0:0);
    (CLK_FIFO_LM => DATA_ADC2[25]) = (0:0:0, 0:0:0);
    (CLK_FIFO_LM => DATA_ADC2[26]) = (0:0:0, 0:0:0);
    (CLK_FIFO_LM => DATA_ADC2[27]) = (0:0:0, 0:0:0);
    (CLK_FIFO_LM => DATA_ADC2[28]) = (0:0:0, 0:0:0);
    (CLK_FIFO_LM => DATA_ADC2[29]) = (0:0:0, 0:0:0);
    (CLK_FIFO_LM => DATA_ADC2[2]) = (0:0:0, 0:0:0);
    (CLK_FIFO_LM => DATA_ADC2[30]) = (0:0:0, 0:0:0);
    (CLK_FIFO_LM => DATA_ADC2[31]) = (0:0:0, 0:0:0);
    (CLK_FIFO_LM => DATA_ADC2[32]) = (0:0:0, 0:0:0);
    (CLK_FIFO_LM => DATA_ADC2[33]) = (0:0:0, 0:0:0);
    (CLK_FIFO_LM => DATA_ADC2[34]) = (0:0:0, 0:0:0);
    (CLK_FIFO_LM => DATA_ADC2[35]) = (0:0:0, 0:0:0);
    (CLK_FIFO_LM => DATA_ADC2[36]) = (0:0:0, 0:0:0);
    (CLK_FIFO_LM => DATA_ADC2[37]) = (0:0:0, 0:0:0);
    (CLK_FIFO_LM => DATA_ADC2[38]) = (0:0:0, 0:0:0);
    (CLK_FIFO_LM => DATA_ADC2[39]) = (0:0:0, 0:0:0);
    (CLK_FIFO_LM => DATA_ADC2[3]) = (0:0:0, 0:0:0);
    (CLK_FIFO_LM => DATA_ADC2[40]) = (0:0:0, 0:0:0);
    (CLK_FIFO_LM => DATA_ADC2[41]) = (0:0:0, 0:0:0);
    (CLK_FIFO_LM => DATA_ADC2[42]) = (0:0:0, 0:0:0);
    (CLK_FIFO_LM => DATA_ADC2[43]) = (0:0:0, 0:0:0);
    (CLK_FIFO_LM => DATA_ADC2[44]) = (0:0:0, 0:0:0);
    (CLK_FIFO_LM => DATA_ADC2[45]) = (0:0:0, 0:0:0);
    (CLK_FIFO_LM => DATA_ADC2[46]) = (0:0:0, 0:0:0);
    (CLK_FIFO_LM => DATA_ADC2[47]) = (0:0:0, 0:0:0);
    (CLK_FIFO_LM => DATA_ADC2[48]) = (0:0:0, 0:0:0);
    (CLK_FIFO_LM => DATA_ADC2[49]) = (0:0:0, 0:0:0);
    (CLK_FIFO_LM => DATA_ADC2[4]) = (0:0:0, 0:0:0);
    (CLK_FIFO_LM => DATA_ADC2[50]) = (0:0:0, 0:0:0);
    (CLK_FIFO_LM => DATA_ADC2[51]) = (0:0:0, 0:0:0);
    (CLK_FIFO_LM => DATA_ADC2[52]) = (0:0:0, 0:0:0);
    (CLK_FIFO_LM => DATA_ADC2[53]) = (0:0:0, 0:0:0);
    (CLK_FIFO_LM => DATA_ADC2[54]) = (0:0:0, 0:0:0);
    (CLK_FIFO_LM => DATA_ADC2[55]) = (0:0:0, 0:0:0);
    (CLK_FIFO_LM => DATA_ADC2[56]) = (0:0:0, 0:0:0);
    (CLK_FIFO_LM => DATA_ADC2[57]) = (0:0:0, 0:0:0);
    (CLK_FIFO_LM => DATA_ADC2[58]) = (0:0:0, 0:0:0);
    (CLK_FIFO_LM => DATA_ADC2[59]) = (0:0:0, 0:0:0);
    (CLK_FIFO_LM => DATA_ADC2[5]) = (0:0:0, 0:0:0);
    (CLK_FIFO_LM => DATA_ADC2[60]) = (0:0:0, 0:0:0);
    (CLK_FIFO_LM => DATA_ADC2[61]) = (0:0:0, 0:0:0);
    (CLK_FIFO_LM => DATA_ADC2[62]) = (0:0:0, 0:0:0);
    (CLK_FIFO_LM => DATA_ADC2[63]) = (0:0:0, 0:0:0);
    (CLK_FIFO_LM => DATA_ADC2[64]) = (0:0:0, 0:0:0);
    (CLK_FIFO_LM => DATA_ADC2[65]) = (0:0:0, 0:0:0);
    (CLK_FIFO_LM => DATA_ADC2[66]) = (0:0:0, 0:0:0);
    (CLK_FIFO_LM => DATA_ADC2[67]) = (0:0:0, 0:0:0);
    (CLK_FIFO_LM => DATA_ADC2[68]) = (0:0:0, 0:0:0);
    (CLK_FIFO_LM => DATA_ADC2[69]) = (0:0:0, 0:0:0);
    (CLK_FIFO_LM => DATA_ADC2[6]) = (0:0:0, 0:0:0);
    (CLK_FIFO_LM => DATA_ADC2[70]) = (0:0:0, 0:0:0);
    (CLK_FIFO_LM => DATA_ADC2[71]) = (0:0:0, 0:0:0);
    (CLK_FIFO_LM => DATA_ADC2[72]) = (0:0:0, 0:0:0);
    (CLK_FIFO_LM => DATA_ADC2[73]) = (0:0:0, 0:0:0);
    (CLK_FIFO_LM => DATA_ADC2[74]) = (0:0:0, 0:0:0);
    (CLK_FIFO_LM => DATA_ADC2[75]) = (0:0:0, 0:0:0);
    (CLK_FIFO_LM => DATA_ADC2[76]) = (0:0:0, 0:0:0);
    (CLK_FIFO_LM => DATA_ADC2[77]) = (0:0:0, 0:0:0);
    (CLK_FIFO_LM => DATA_ADC2[78]) = (0:0:0, 0:0:0);
    (CLK_FIFO_LM => DATA_ADC2[79]) = (0:0:0, 0:0:0);
    (CLK_FIFO_LM => DATA_ADC2[7]) = (0:0:0, 0:0:0);
    (CLK_FIFO_LM => DATA_ADC2[80]) = (0:0:0, 0:0:0);
    (CLK_FIFO_LM => DATA_ADC2[81]) = (0:0:0, 0:0:0);
    (CLK_FIFO_LM => DATA_ADC2[82]) = (0:0:0, 0:0:0);
    (CLK_FIFO_LM => DATA_ADC2[83]) = (0:0:0, 0:0:0);
    (CLK_FIFO_LM => DATA_ADC2[84]) = (0:0:0, 0:0:0);
    (CLK_FIFO_LM => DATA_ADC2[85]) = (0:0:0, 0:0:0);
    (CLK_FIFO_LM => DATA_ADC2[86]) = (0:0:0, 0:0:0);
    (CLK_FIFO_LM => DATA_ADC2[87]) = (0:0:0, 0:0:0);
    (CLK_FIFO_LM => DATA_ADC2[88]) = (0:0:0, 0:0:0);
    (CLK_FIFO_LM => DATA_ADC2[89]) = (0:0:0, 0:0:0);
    (CLK_FIFO_LM => DATA_ADC2[8]) = (0:0:0, 0:0:0);
    (CLK_FIFO_LM => DATA_ADC2[90]) = (0:0:0, 0:0:0);
    (CLK_FIFO_LM => DATA_ADC2[91]) = (0:0:0, 0:0:0);
    (CLK_FIFO_LM => DATA_ADC2[92]) = (0:0:0, 0:0:0);
    (CLK_FIFO_LM => DATA_ADC2[93]) = (0:0:0, 0:0:0);
    (CLK_FIFO_LM => DATA_ADC2[94]) = (0:0:0, 0:0:0);
    (CLK_FIFO_LM => DATA_ADC2[95]) = (0:0:0, 0:0:0);
    (CLK_FIFO_LM => DATA_ADC2[96]) = (0:0:0, 0:0:0);
    (CLK_FIFO_LM => DATA_ADC2[97]) = (0:0:0, 0:0:0);
    (CLK_FIFO_LM => DATA_ADC2[98]) = (0:0:0, 0:0:0);
    (CLK_FIFO_LM => DATA_ADC2[99]) = (0:0:0, 0:0:0);
    (CLK_FIFO_LM => DATA_ADC2[9]) = (0:0:0, 0:0:0);
    (CLK_FIFO_LM => DATA_ADC3[0]) = (0:0:0, 0:0:0);
    (CLK_FIFO_LM => DATA_ADC3[100]) = (0:0:0, 0:0:0);
    (CLK_FIFO_LM => DATA_ADC3[101]) = (0:0:0, 0:0:0);
    (CLK_FIFO_LM => DATA_ADC3[102]) = (0:0:0, 0:0:0);
    (CLK_FIFO_LM => DATA_ADC3[103]) = (0:0:0, 0:0:0);
    (CLK_FIFO_LM => DATA_ADC3[104]) = (0:0:0, 0:0:0);
    (CLK_FIFO_LM => DATA_ADC3[105]) = (0:0:0, 0:0:0);
    (CLK_FIFO_LM => DATA_ADC3[106]) = (0:0:0, 0:0:0);
    (CLK_FIFO_LM => DATA_ADC3[107]) = (0:0:0, 0:0:0);
    (CLK_FIFO_LM => DATA_ADC3[108]) = (0:0:0, 0:0:0);
    (CLK_FIFO_LM => DATA_ADC3[109]) = (0:0:0, 0:0:0);
    (CLK_FIFO_LM => DATA_ADC3[10]) = (0:0:0, 0:0:0);
    (CLK_FIFO_LM => DATA_ADC3[110]) = (0:0:0, 0:0:0);
    (CLK_FIFO_LM => DATA_ADC3[111]) = (0:0:0, 0:0:0);
    (CLK_FIFO_LM => DATA_ADC3[112]) = (0:0:0, 0:0:0);
    (CLK_FIFO_LM => DATA_ADC3[113]) = (0:0:0, 0:0:0);
    (CLK_FIFO_LM => DATA_ADC3[114]) = (0:0:0, 0:0:0);
    (CLK_FIFO_LM => DATA_ADC3[115]) = (0:0:0, 0:0:0);
    (CLK_FIFO_LM => DATA_ADC3[116]) = (0:0:0, 0:0:0);
    (CLK_FIFO_LM => DATA_ADC3[117]) = (0:0:0, 0:0:0);
    (CLK_FIFO_LM => DATA_ADC3[118]) = (0:0:0, 0:0:0);
    (CLK_FIFO_LM => DATA_ADC3[119]) = (0:0:0, 0:0:0);
    (CLK_FIFO_LM => DATA_ADC3[11]) = (0:0:0, 0:0:0);
    (CLK_FIFO_LM => DATA_ADC3[120]) = (0:0:0, 0:0:0);
    (CLK_FIFO_LM => DATA_ADC3[121]) = (0:0:0, 0:0:0);
    (CLK_FIFO_LM => DATA_ADC3[122]) = (0:0:0, 0:0:0);
    (CLK_FIFO_LM => DATA_ADC3[123]) = (0:0:0, 0:0:0);
    (CLK_FIFO_LM => DATA_ADC3[124]) = (0:0:0, 0:0:0);
    (CLK_FIFO_LM => DATA_ADC3[125]) = (0:0:0, 0:0:0);
    (CLK_FIFO_LM => DATA_ADC3[126]) = (0:0:0, 0:0:0);
    (CLK_FIFO_LM => DATA_ADC3[127]) = (0:0:0, 0:0:0);
    (CLK_FIFO_LM => DATA_ADC3[128]) = (0:0:0, 0:0:0);
    (CLK_FIFO_LM => DATA_ADC3[129]) = (0:0:0, 0:0:0);
    (CLK_FIFO_LM => DATA_ADC3[12]) = (0:0:0, 0:0:0);
    (CLK_FIFO_LM => DATA_ADC3[130]) = (0:0:0, 0:0:0);
    (CLK_FIFO_LM => DATA_ADC3[131]) = (0:0:0, 0:0:0);
    (CLK_FIFO_LM => DATA_ADC3[132]) = (0:0:0, 0:0:0);
    (CLK_FIFO_LM => DATA_ADC3[133]) = (0:0:0, 0:0:0);
    (CLK_FIFO_LM => DATA_ADC3[134]) = (0:0:0, 0:0:0);
    (CLK_FIFO_LM => DATA_ADC3[135]) = (0:0:0, 0:0:0);
    (CLK_FIFO_LM => DATA_ADC3[136]) = (0:0:0, 0:0:0);
    (CLK_FIFO_LM => DATA_ADC3[137]) = (0:0:0, 0:0:0);
    (CLK_FIFO_LM => DATA_ADC3[138]) = (0:0:0, 0:0:0);
    (CLK_FIFO_LM => DATA_ADC3[139]) = (0:0:0, 0:0:0);
    (CLK_FIFO_LM => DATA_ADC3[13]) = (0:0:0, 0:0:0);
    (CLK_FIFO_LM => DATA_ADC3[140]) = (0:0:0, 0:0:0);
    (CLK_FIFO_LM => DATA_ADC3[141]) = (0:0:0, 0:0:0);
    (CLK_FIFO_LM => DATA_ADC3[142]) = (0:0:0, 0:0:0);
    (CLK_FIFO_LM => DATA_ADC3[143]) = (0:0:0, 0:0:0);
    (CLK_FIFO_LM => DATA_ADC3[144]) = (0:0:0, 0:0:0);
    (CLK_FIFO_LM => DATA_ADC3[145]) = (0:0:0, 0:0:0);
    (CLK_FIFO_LM => DATA_ADC3[146]) = (0:0:0, 0:0:0);
    (CLK_FIFO_LM => DATA_ADC3[147]) = (0:0:0, 0:0:0);
    (CLK_FIFO_LM => DATA_ADC3[148]) = (0:0:0, 0:0:0);
    (CLK_FIFO_LM => DATA_ADC3[149]) = (0:0:0, 0:0:0);
    (CLK_FIFO_LM => DATA_ADC3[14]) = (0:0:0, 0:0:0);
    (CLK_FIFO_LM => DATA_ADC3[150]) = (0:0:0, 0:0:0);
    (CLK_FIFO_LM => DATA_ADC3[151]) = (0:0:0, 0:0:0);
    (CLK_FIFO_LM => DATA_ADC3[152]) = (0:0:0, 0:0:0);
    (CLK_FIFO_LM => DATA_ADC3[153]) = (0:0:0, 0:0:0);
    (CLK_FIFO_LM => DATA_ADC3[154]) = (0:0:0, 0:0:0);
    (CLK_FIFO_LM => DATA_ADC3[155]) = (0:0:0, 0:0:0);
    (CLK_FIFO_LM => DATA_ADC3[156]) = (0:0:0, 0:0:0);
    (CLK_FIFO_LM => DATA_ADC3[157]) = (0:0:0, 0:0:0);
    (CLK_FIFO_LM => DATA_ADC3[158]) = (0:0:0, 0:0:0);
    (CLK_FIFO_LM => DATA_ADC3[159]) = (0:0:0, 0:0:0);
    (CLK_FIFO_LM => DATA_ADC3[15]) = (0:0:0, 0:0:0);
    (CLK_FIFO_LM => DATA_ADC3[160]) = (0:0:0, 0:0:0);
    (CLK_FIFO_LM => DATA_ADC3[161]) = (0:0:0, 0:0:0);
    (CLK_FIFO_LM => DATA_ADC3[162]) = (0:0:0, 0:0:0);
    (CLK_FIFO_LM => DATA_ADC3[163]) = (0:0:0, 0:0:0);
    (CLK_FIFO_LM => DATA_ADC3[164]) = (0:0:0, 0:0:0);
    (CLK_FIFO_LM => DATA_ADC3[165]) = (0:0:0, 0:0:0);
    (CLK_FIFO_LM => DATA_ADC3[166]) = (0:0:0, 0:0:0);
    (CLK_FIFO_LM => DATA_ADC3[167]) = (0:0:0, 0:0:0);
    (CLK_FIFO_LM => DATA_ADC3[168]) = (0:0:0, 0:0:0);
    (CLK_FIFO_LM => DATA_ADC3[169]) = (0:0:0, 0:0:0);
    (CLK_FIFO_LM => DATA_ADC3[16]) = (0:0:0, 0:0:0);
    (CLK_FIFO_LM => DATA_ADC3[170]) = (0:0:0, 0:0:0);
    (CLK_FIFO_LM => DATA_ADC3[171]) = (0:0:0, 0:0:0);
    (CLK_FIFO_LM => DATA_ADC3[172]) = (0:0:0, 0:0:0);
    (CLK_FIFO_LM => DATA_ADC3[173]) = (0:0:0, 0:0:0);
    (CLK_FIFO_LM => DATA_ADC3[174]) = (0:0:0, 0:0:0);
    (CLK_FIFO_LM => DATA_ADC3[175]) = (0:0:0, 0:0:0);
    (CLK_FIFO_LM => DATA_ADC3[176]) = (0:0:0, 0:0:0);
    (CLK_FIFO_LM => DATA_ADC3[177]) = (0:0:0, 0:0:0);
    (CLK_FIFO_LM => DATA_ADC3[178]) = (0:0:0, 0:0:0);
    (CLK_FIFO_LM => DATA_ADC3[179]) = (0:0:0, 0:0:0);
    (CLK_FIFO_LM => DATA_ADC3[17]) = (0:0:0, 0:0:0);
    (CLK_FIFO_LM => DATA_ADC3[180]) = (0:0:0, 0:0:0);
    (CLK_FIFO_LM => DATA_ADC3[181]) = (0:0:0, 0:0:0);
    (CLK_FIFO_LM => DATA_ADC3[182]) = (0:0:0, 0:0:0);
    (CLK_FIFO_LM => DATA_ADC3[183]) = (0:0:0, 0:0:0);
    (CLK_FIFO_LM => DATA_ADC3[184]) = (0:0:0, 0:0:0);
    (CLK_FIFO_LM => DATA_ADC3[185]) = (0:0:0, 0:0:0);
    (CLK_FIFO_LM => DATA_ADC3[186]) = (0:0:0, 0:0:0);
    (CLK_FIFO_LM => DATA_ADC3[187]) = (0:0:0, 0:0:0);
    (CLK_FIFO_LM => DATA_ADC3[188]) = (0:0:0, 0:0:0);
    (CLK_FIFO_LM => DATA_ADC3[189]) = (0:0:0, 0:0:0);
    (CLK_FIFO_LM => DATA_ADC3[18]) = (0:0:0, 0:0:0);
    (CLK_FIFO_LM => DATA_ADC3[190]) = (0:0:0, 0:0:0);
    (CLK_FIFO_LM => DATA_ADC3[191]) = (0:0:0, 0:0:0);
    (CLK_FIFO_LM => DATA_ADC3[19]) = (0:0:0, 0:0:0);
    (CLK_FIFO_LM => DATA_ADC3[1]) = (0:0:0, 0:0:0);
    (CLK_FIFO_LM => DATA_ADC3[20]) = (0:0:0, 0:0:0);
    (CLK_FIFO_LM => DATA_ADC3[21]) = (0:0:0, 0:0:0);
    (CLK_FIFO_LM => DATA_ADC3[22]) = (0:0:0, 0:0:0);
    (CLK_FIFO_LM => DATA_ADC3[23]) = (0:0:0, 0:0:0);
    (CLK_FIFO_LM => DATA_ADC3[24]) = (0:0:0, 0:0:0);
    (CLK_FIFO_LM => DATA_ADC3[25]) = (0:0:0, 0:0:0);
    (CLK_FIFO_LM => DATA_ADC3[26]) = (0:0:0, 0:0:0);
    (CLK_FIFO_LM => DATA_ADC3[27]) = (0:0:0, 0:0:0);
    (CLK_FIFO_LM => DATA_ADC3[28]) = (0:0:0, 0:0:0);
    (CLK_FIFO_LM => DATA_ADC3[29]) = (0:0:0, 0:0:0);
    (CLK_FIFO_LM => DATA_ADC3[2]) = (0:0:0, 0:0:0);
    (CLK_FIFO_LM => DATA_ADC3[30]) = (0:0:0, 0:0:0);
    (CLK_FIFO_LM => DATA_ADC3[31]) = (0:0:0, 0:0:0);
    (CLK_FIFO_LM => DATA_ADC3[32]) = (0:0:0, 0:0:0);
    (CLK_FIFO_LM => DATA_ADC3[33]) = (0:0:0, 0:0:0);
    (CLK_FIFO_LM => DATA_ADC3[34]) = (0:0:0, 0:0:0);
    (CLK_FIFO_LM => DATA_ADC3[35]) = (0:0:0, 0:0:0);
    (CLK_FIFO_LM => DATA_ADC3[36]) = (0:0:0, 0:0:0);
    (CLK_FIFO_LM => DATA_ADC3[37]) = (0:0:0, 0:0:0);
    (CLK_FIFO_LM => DATA_ADC3[38]) = (0:0:0, 0:0:0);
    (CLK_FIFO_LM => DATA_ADC3[39]) = (0:0:0, 0:0:0);
    (CLK_FIFO_LM => DATA_ADC3[3]) = (0:0:0, 0:0:0);
    (CLK_FIFO_LM => DATA_ADC3[40]) = (0:0:0, 0:0:0);
    (CLK_FIFO_LM => DATA_ADC3[41]) = (0:0:0, 0:0:0);
    (CLK_FIFO_LM => DATA_ADC3[42]) = (0:0:0, 0:0:0);
    (CLK_FIFO_LM => DATA_ADC3[43]) = (0:0:0, 0:0:0);
    (CLK_FIFO_LM => DATA_ADC3[44]) = (0:0:0, 0:0:0);
    (CLK_FIFO_LM => DATA_ADC3[45]) = (0:0:0, 0:0:0);
    (CLK_FIFO_LM => DATA_ADC3[46]) = (0:0:0, 0:0:0);
    (CLK_FIFO_LM => DATA_ADC3[47]) = (0:0:0, 0:0:0);
    (CLK_FIFO_LM => DATA_ADC3[48]) = (0:0:0, 0:0:0);
    (CLK_FIFO_LM => DATA_ADC3[49]) = (0:0:0, 0:0:0);
    (CLK_FIFO_LM => DATA_ADC3[4]) = (0:0:0, 0:0:0);
    (CLK_FIFO_LM => DATA_ADC3[50]) = (0:0:0, 0:0:0);
    (CLK_FIFO_LM => DATA_ADC3[51]) = (0:0:0, 0:0:0);
    (CLK_FIFO_LM => DATA_ADC3[52]) = (0:0:0, 0:0:0);
    (CLK_FIFO_LM => DATA_ADC3[53]) = (0:0:0, 0:0:0);
    (CLK_FIFO_LM => DATA_ADC3[54]) = (0:0:0, 0:0:0);
    (CLK_FIFO_LM => DATA_ADC3[55]) = (0:0:0, 0:0:0);
    (CLK_FIFO_LM => DATA_ADC3[56]) = (0:0:0, 0:0:0);
    (CLK_FIFO_LM => DATA_ADC3[57]) = (0:0:0, 0:0:0);
    (CLK_FIFO_LM => DATA_ADC3[58]) = (0:0:0, 0:0:0);
    (CLK_FIFO_LM => DATA_ADC3[59]) = (0:0:0, 0:0:0);
    (CLK_FIFO_LM => DATA_ADC3[5]) = (0:0:0, 0:0:0);
    (CLK_FIFO_LM => DATA_ADC3[60]) = (0:0:0, 0:0:0);
    (CLK_FIFO_LM => DATA_ADC3[61]) = (0:0:0, 0:0:0);
    (CLK_FIFO_LM => DATA_ADC3[62]) = (0:0:0, 0:0:0);
    (CLK_FIFO_LM => DATA_ADC3[63]) = (0:0:0, 0:0:0);
    (CLK_FIFO_LM => DATA_ADC3[64]) = (0:0:0, 0:0:0);
    (CLK_FIFO_LM => DATA_ADC3[65]) = (0:0:0, 0:0:0);
    (CLK_FIFO_LM => DATA_ADC3[66]) = (0:0:0, 0:0:0);
    (CLK_FIFO_LM => DATA_ADC3[67]) = (0:0:0, 0:0:0);
    (CLK_FIFO_LM => DATA_ADC3[68]) = (0:0:0, 0:0:0);
    (CLK_FIFO_LM => DATA_ADC3[69]) = (0:0:0, 0:0:0);
    (CLK_FIFO_LM => DATA_ADC3[6]) = (0:0:0, 0:0:0);
    (CLK_FIFO_LM => DATA_ADC3[70]) = (0:0:0, 0:0:0);
    (CLK_FIFO_LM => DATA_ADC3[71]) = (0:0:0, 0:0:0);
    (CLK_FIFO_LM => DATA_ADC3[72]) = (0:0:0, 0:0:0);
    (CLK_FIFO_LM => DATA_ADC3[73]) = (0:0:0, 0:0:0);
    (CLK_FIFO_LM => DATA_ADC3[74]) = (0:0:0, 0:0:0);
    (CLK_FIFO_LM => DATA_ADC3[75]) = (0:0:0, 0:0:0);
    (CLK_FIFO_LM => DATA_ADC3[76]) = (0:0:0, 0:0:0);
    (CLK_FIFO_LM => DATA_ADC3[77]) = (0:0:0, 0:0:0);
    (CLK_FIFO_LM => DATA_ADC3[78]) = (0:0:0, 0:0:0);
    (CLK_FIFO_LM => DATA_ADC3[79]) = (0:0:0, 0:0:0);
    (CLK_FIFO_LM => DATA_ADC3[7]) = (0:0:0, 0:0:0);
    (CLK_FIFO_LM => DATA_ADC3[80]) = (0:0:0, 0:0:0);
    (CLK_FIFO_LM => DATA_ADC3[81]) = (0:0:0, 0:0:0);
    (CLK_FIFO_LM => DATA_ADC3[82]) = (0:0:0, 0:0:0);
    (CLK_FIFO_LM => DATA_ADC3[83]) = (0:0:0, 0:0:0);
    (CLK_FIFO_LM => DATA_ADC3[84]) = (0:0:0, 0:0:0);
    (CLK_FIFO_LM => DATA_ADC3[85]) = (0:0:0, 0:0:0);
    (CLK_FIFO_LM => DATA_ADC3[86]) = (0:0:0, 0:0:0);
    (CLK_FIFO_LM => DATA_ADC3[87]) = (0:0:0, 0:0:0);
    (CLK_FIFO_LM => DATA_ADC3[88]) = (0:0:0, 0:0:0);
    (CLK_FIFO_LM => DATA_ADC3[89]) = (0:0:0, 0:0:0);
    (CLK_FIFO_LM => DATA_ADC3[8]) = (0:0:0, 0:0:0);
    (CLK_FIFO_LM => DATA_ADC3[90]) = (0:0:0, 0:0:0);
    (CLK_FIFO_LM => DATA_ADC3[91]) = (0:0:0, 0:0:0);
    (CLK_FIFO_LM => DATA_ADC3[92]) = (0:0:0, 0:0:0);
    (CLK_FIFO_LM => DATA_ADC3[93]) = (0:0:0, 0:0:0);
    (CLK_FIFO_LM => DATA_ADC3[94]) = (0:0:0, 0:0:0);
    (CLK_FIFO_LM => DATA_ADC3[95]) = (0:0:0, 0:0:0);
    (CLK_FIFO_LM => DATA_ADC3[96]) = (0:0:0, 0:0:0);
    (CLK_FIFO_LM => DATA_ADC3[97]) = (0:0:0, 0:0:0);
    (CLK_FIFO_LM => DATA_ADC3[98]) = (0:0:0, 0:0:0);
    (CLK_FIFO_LM => DATA_ADC3[99]) = (0:0:0, 0:0:0);
    (CLK_FIFO_LM => DATA_ADC3[9]) = (0:0:0, 0:0:0);
    (CLK_FIFO_LM => STATUS_ADC0[10]) = (0:0:0, 0:0:0);
    (CLK_FIFO_LM => STATUS_ADC0[11]) = (0:0:0, 0:0:0);
    (CLK_FIFO_LM => STATUS_ADC0[12]) = (0:0:0, 0:0:0);
    (CLK_FIFO_LM => STATUS_ADC0[8]) = (0:0:0, 0:0:0);
    (CLK_FIFO_LM => STATUS_ADC0[9]) = (0:0:0, 0:0:0);
    (CLK_FIFO_LM => STATUS_ADC1[10]) = (0:0:0, 0:0:0);
    (CLK_FIFO_LM => STATUS_ADC1[11]) = (0:0:0, 0:0:0);
    (CLK_FIFO_LM => STATUS_ADC1[12]) = (0:0:0, 0:0:0);
    (CLK_FIFO_LM => STATUS_ADC1[8]) = (0:0:0, 0:0:0);
    (CLK_FIFO_LM => STATUS_ADC1[9]) = (0:0:0, 0:0:0);
    (CLK_FIFO_LM => STATUS_ADC2[10]) = (0:0:0, 0:0:0);
    (CLK_FIFO_LM => STATUS_ADC2[11]) = (0:0:0, 0:0:0);
    (CLK_FIFO_LM => STATUS_ADC2[12]) = (0:0:0, 0:0:0);
    (CLK_FIFO_LM => STATUS_ADC2[8]) = (0:0:0, 0:0:0);
    (CLK_FIFO_LM => STATUS_ADC2[9]) = (0:0:0, 0:0:0);
    (CLK_FIFO_LM => STATUS_ADC3[10]) = (0:0:0, 0:0:0);
    (CLK_FIFO_LM => STATUS_ADC3[11]) = (0:0:0, 0:0:0);
    (CLK_FIFO_LM => STATUS_ADC3[12]) = (0:0:0, 0:0:0);
    (CLK_FIFO_LM => STATUS_ADC3[8]) = (0:0:0, 0:0:0);
    (CLK_FIFO_LM => STATUS_ADC3[9]) = (0:0:0, 0:0:0);
    (DCLK => DOUT[0]) = (100:100:100, 100:100:100);
    (DCLK => DOUT[10]) = (100:100:100, 100:100:100);
    (DCLK => DOUT[11]) = (100:100:100, 100:100:100);
    (DCLK => DOUT[12]) = (100:100:100, 100:100:100);
    (DCLK => DOUT[13]) = (100:100:100, 100:100:100);
    (DCLK => DOUT[14]) = (100:100:100, 100:100:100);
    (DCLK => DOUT[15]) = (100:100:100, 100:100:100);
    (DCLK => DOUT[1]) = (100:100:100, 100:100:100);
    (DCLK => DOUT[2]) = (100:100:100, 100:100:100);
    (DCLK => DOUT[3]) = (100:100:100, 100:100:100);
    (DCLK => DOUT[4]) = (100:100:100, 100:100:100);
    (DCLK => DOUT[5]) = (100:100:100, 100:100:100);
    (DCLK => DOUT[6]) = (100:100:100, 100:100:100);
    (DCLK => DOUT[7]) = (100:100:100, 100:100:100);
    (DCLK => DOUT[8]) = (100:100:100, 100:100:100);
    (DCLK => DOUT[9]) = (100:100:100, 100:100:100);
    (DCLK => DRDY) = (100:100:100, 100:100:100);
    (DCLK => STATUS_COMMON[6]) = (100:100:100, 100:100:100);
    (FABRIC_CLK => DATA_ADC0[0]) = (100:100:100, 100:100:100);
    (FABRIC_CLK => DATA_ADC0[100]) = (100:100:100, 100:100:100);
    (FABRIC_CLK => DATA_ADC0[101]) = (100:100:100, 100:100:100);
    (FABRIC_CLK => DATA_ADC0[102]) = (100:100:100, 100:100:100);
    (FABRIC_CLK => DATA_ADC0[103]) = (100:100:100, 100:100:100);
    (FABRIC_CLK => DATA_ADC0[104]) = (100:100:100, 100:100:100);
    (FABRIC_CLK => DATA_ADC0[105]) = (100:100:100, 100:100:100);
    (FABRIC_CLK => DATA_ADC0[106]) = (100:100:100, 100:100:100);
    (FABRIC_CLK => DATA_ADC0[107]) = (100:100:100, 100:100:100);
    (FABRIC_CLK => DATA_ADC0[108]) = (100:100:100, 100:100:100);
    (FABRIC_CLK => DATA_ADC0[109]) = (100:100:100, 100:100:100);
    (FABRIC_CLK => DATA_ADC0[10]) = (100:100:100, 100:100:100);
    (FABRIC_CLK => DATA_ADC0[110]) = (100:100:100, 100:100:100);
    (FABRIC_CLK => DATA_ADC0[111]) = (100:100:100, 100:100:100);
    (FABRIC_CLK => DATA_ADC0[112]) = (100:100:100, 100:100:100);
    (FABRIC_CLK => DATA_ADC0[113]) = (100:100:100, 100:100:100);
    (FABRIC_CLK => DATA_ADC0[114]) = (100:100:100, 100:100:100);
    (FABRIC_CLK => DATA_ADC0[115]) = (100:100:100, 100:100:100);
    (FABRIC_CLK => DATA_ADC0[116]) = (100:100:100, 100:100:100);
    (FABRIC_CLK => DATA_ADC0[117]) = (100:100:100, 100:100:100);
    (FABRIC_CLK => DATA_ADC0[118]) = (100:100:100, 100:100:100);
    (FABRIC_CLK => DATA_ADC0[119]) = (100:100:100, 100:100:100);
    (FABRIC_CLK => DATA_ADC0[11]) = (100:100:100, 100:100:100);
    (FABRIC_CLK => DATA_ADC0[120]) = (100:100:100, 100:100:100);
    (FABRIC_CLK => DATA_ADC0[121]) = (100:100:100, 100:100:100);
    (FABRIC_CLK => DATA_ADC0[122]) = (100:100:100, 100:100:100);
    (FABRIC_CLK => DATA_ADC0[123]) = (100:100:100, 100:100:100);
    (FABRIC_CLK => DATA_ADC0[124]) = (100:100:100, 100:100:100);
    (FABRIC_CLK => DATA_ADC0[125]) = (100:100:100, 100:100:100);
    (FABRIC_CLK => DATA_ADC0[126]) = (100:100:100, 100:100:100);
    (FABRIC_CLK => DATA_ADC0[127]) = (100:100:100, 100:100:100);
    (FABRIC_CLK => DATA_ADC0[128]) = (100:100:100, 100:100:100);
    (FABRIC_CLK => DATA_ADC0[129]) = (100:100:100, 100:100:100);
    (FABRIC_CLK => DATA_ADC0[12]) = (100:100:100, 100:100:100);
    (FABRIC_CLK => DATA_ADC0[130]) = (100:100:100, 100:100:100);
    (FABRIC_CLK => DATA_ADC0[131]) = (100:100:100, 100:100:100);
    (FABRIC_CLK => DATA_ADC0[132]) = (100:100:100, 100:100:100);
    (FABRIC_CLK => DATA_ADC0[133]) = (100:100:100, 100:100:100);
    (FABRIC_CLK => DATA_ADC0[134]) = (100:100:100, 100:100:100);
    (FABRIC_CLK => DATA_ADC0[135]) = (100:100:100, 100:100:100);
    (FABRIC_CLK => DATA_ADC0[136]) = (100:100:100, 100:100:100);
    (FABRIC_CLK => DATA_ADC0[137]) = (100:100:100, 100:100:100);
    (FABRIC_CLK => DATA_ADC0[138]) = (100:100:100, 100:100:100);
    (FABRIC_CLK => DATA_ADC0[139]) = (100:100:100, 100:100:100);
    (FABRIC_CLK => DATA_ADC0[13]) = (100:100:100, 100:100:100);
    (FABRIC_CLK => DATA_ADC0[140]) = (100:100:100, 100:100:100);
    (FABRIC_CLK => DATA_ADC0[141]) = (100:100:100, 100:100:100);
    (FABRIC_CLK => DATA_ADC0[142]) = (100:100:100, 100:100:100);
    (FABRIC_CLK => DATA_ADC0[143]) = (100:100:100, 100:100:100);
    (FABRIC_CLK => DATA_ADC0[144]) = (100:100:100, 100:100:100);
    (FABRIC_CLK => DATA_ADC0[145]) = (100:100:100, 100:100:100);
    (FABRIC_CLK => DATA_ADC0[146]) = (100:100:100, 100:100:100);
    (FABRIC_CLK => DATA_ADC0[147]) = (100:100:100, 100:100:100);
    (FABRIC_CLK => DATA_ADC0[148]) = (100:100:100, 100:100:100);
    (FABRIC_CLK => DATA_ADC0[149]) = (100:100:100, 100:100:100);
    (FABRIC_CLK => DATA_ADC0[14]) = (100:100:100, 100:100:100);
    (FABRIC_CLK => DATA_ADC0[150]) = (100:100:100, 100:100:100);
    (FABRIC_CLK => DATA_ADC0[151]) = (100:100:100, 100:100:100);
    (FABRIC_CLK => DATA_ADC0[152]) = (100:100:100, 100:100:100);
    (FABRIC_CLK => DATA_ADC0[153]) = (100:100:100, 100:100:100);
    (FABRIC_CLK => DATA_ADC0[154]) = (100:100:100, 100:100:100);
    (FABRIC_CLK => DATA_ADC0[155]) = (100:100:100, 100:100:100);
    (FABRIC_CLK => DATA_ADC0[156]) = (100:100:100, 100:100:100);
    (FABRIC_CLK => DATA_ADC0[157]) = (100:100:100, 100:100:100);
    (FABRIC_CLK => DATA_ADC0[158]) = (100:100:100, 100:100:100);
    (FABRIC_CLK => DATA_ADC0[159]) = (100:100:100, 100:100:100);
    (FABRIC_CLK => DATA_ADC0[15]) = (100:100:100, 100:100:100);
    (FABRIC_CLK => DATA_ADC0[160]) = (100:100:100, 100:100:100);
    (FABRIC_CLK => DATA_ADC0[161]) = (100:100:100, 100:100:100);
    (FABRIC_CLK => DATA_ADC0[162]) = (100:100:100, 100:100:100);
    (FABRIC_CLK => DATA_ADC0[163]) = (100:100:100, 100:100:100);
    (FABRIC_CLK => DATA_ADC0[164]) = (100:100:100, 100:100:100);
    (FABRIC_CLK => DATA_ADC0[165]) = (100:100:100, 100:100:100);
    (FABRIC_CLK => DATA_ADC0[166]) = (100:100:100, 100:100:100);
    (FABRIC_CLK => DATA_ADC0[167]) = (100:100:100, 100:100:100);
    (FABRIC_CLK => DATA_ADC0[168]) = (100:100:100, 100:100:100);
    (FABRIC_CLK => DATA_ADC0[169]) = (100:100:100, 100:100:100);
    (FABRIC_CLK => DATA_ADC0[16]) = (100:100:100, 100:100:100);
    (FABRIC_CLK => DATA_ADC0[170]) = (100:100:100, 100:100:100);
    (FABRIC_CLK => DATA_ADC0[171]) = (100:100:100, 100:100:100);
    (FABRIC_CLK => DATA_ADC0[172]) = (100:100:100, 100:100:100);
    (FABRIC_CLK => DATA_ADC0[173]) = (100:100:100, 100:100:100);
    (FABRIC_CLK => DATA_ADC0[174]) = (100:100:100, 100:100:100);
    (FABRIC_CLK => DATA_ADC0[175]) = (100:100:100, 100:100:100);
    (FABRIC_CLK => DATA_ADC0[176]) = (100:100:100, 100:100:100);
    (FABRIC_CLK => DATA_ADC0[177]) = (100:100:100, 100:100:100);
    (FABRIC_CLK => DATA_ADC0[178]) = (100:100:100, 100:100:100);
    (FABRIC_CLK => DATA_ADC0[179]) = (100:100:100, 100:100:100);
    (FABRIC_CLK => DATA_ADC0[17]) = (100:100:100, 100:100:100);
    (FABRIC_CLK => DATA_ADC0[180]) = (100:100:100, 100:100:100);
    (FABRIC_CLK => DATA_ADC0[181]) = (100:100:100, 100:100:100);
    (FABRIC_CLK => DATA_ADC0[182]) = (100:100:100, 100:100:100);
    (FABRIC_CLK => DATA_ADC0[183]) = (100:100:100, 100:100:100);
    (FABRIC_CLK => DATA_ADC0[184]) = (100:100:100, 100:100:100);
    (FABRIC_CLK => DATA_ADC0[185]) = (100:100:100, 100:100:100);
    (FABRIC_CLK => DATA_ADC0[186]) = (100:100:100, 100:100:100);
    (FABRIC_CLK => DATA_ADC0[187]) = (100:100:100, 100:100:100);
    (FABRIC_CLK => DATA_ADC0[188]) = (100:100:100, 100:100:100);
    (FABRIC_CLK => DATA_ADC0[189]) = (100:100:100, 100:100:100);
    (FABRIC_CLK => DATA_ADC0[18]) = (100:100:100, 100:100:100);
    (FABRIC_CLK => DATA_ADC0[190]) = (100:100:100, 100:100:100);
    (FABRIC_CLK => DATA_ADC0[191]) = (100:100:100, 100:100:100);
    (FABRIC_CLK => DATA_ADC0[19]) = (100:100:100, 100:100:100);
    (FABRIC_CLK => DATA_ADC0[1]) = (100:100:100, 100:100:100);
    (FABRIC_CLK => DATA_ADC0[20]) = (100:100:100, 100:100:100);
    (FABRIC_CLK => DATA_ADC0[21]) = (100:100:100, 100:100:100);
    (FABRIC_CLK => DATA_ADC0[22]) = (100:100:100, 100:100:100);
    (FABRIC_CLK => DATA_ADC0[23]) = (100:100:100, 100:100:100);
    (FABRIC_CLK => DATA_ADC0[24]) = (100:100:100, 100:100:100);
    (FABRIC_CLK => DATA_ADC0[25]) = (100:100:100, 100:100:100);
    (FABRIC_CLK => DATA_ADC0[26]) = (100:100:100, 100:100:100);
    (FABRIC_CLK => DATA_ADC0[27]) = (100:100:100, 100:100:100);
    (FABRIC_CLK => DATA_ADC0[28]) = (100:100:100, 100:100:100);
    (FABRIC_CLK => DATA_ADC0[29]) = (100:100:100, 100:100:100);
    (FABRIC_CLK => DATA_ADC0[2]) = (100:100:100, 100:100:100);
    (FABRIC_CLK => DATA_ADC0[30]) = (100:100:100, 100:100:100);
    (FABRIC_CLK => DATA_ADC0[31]) = (100:100:100, 100:100:100);
    (FABRIC_CLK => DATA_ADC0[32]) = (100:100:100, 100:100:100);
    (FABRIC_CLK => DATA_ADC0[33]) = (100:100:100, 100:100:100);
    (FABRIC_CLK => DATA_ADC0[34]) = (100:100:100, 100:100:100);
    (FABRIC_CLK => DATA_ADC0[35]) = (100:100:100, 100:100:100);
    (FABRIC_CLK => DATA_ADC0[36]) = (100:100:100, 100:100:100);
    (FABRIC_CLK => DATA_ADC0[37]) = (100:100:100, 100:100:100);
    (FABRIC_CLK => DATA_ADC0[38]) = (100:100:100, 100:100:100);
    (FABRIC_CLK => DATA_ADC0[39]) = (100:100:100, 100:100:100);
    (FABRIC_CLK => DATA_ADC0[3]) = (100:100:100, 100:100:100);
    (FABRIC_CLK => DATA_ADC0[40]) = (100:100:100, 100:100:100);
    (FABRIC_CLK => DATA_ADC0[41]) = (100:100:100, 100:100:100);
    (FABRIC_CLK => DATA_ADC0[42]) = (100:100:100, 100:100:100);
    (FABRIC_CLK => DATA_ADC0[43]) = (100:100:100, 100:100:100);
    (FABRIC_CLK => DATA_ADC0[44]) = (100:100:100, 100:100:100);
    (FABRIC_CLK => DATA_ADC0[45]) = (100:100:100, 100:100:100);
    (FABRIC_CLK => DATA_ADC0[46]) = (100:100:100, 100:100:100);
    (FABRIC_CLK => DATA_ADC0[47]) = (100:100:100, 100:100:100);
    (FABRIC_CLK => DATA_ADC0[48]) = (100:100:100, 100:100:100);
    (FABRIC_CLK => DATA_ADC0[49]) = (100:100:100, 100:100:100);
    (FABRIC_CLK => DATA_ADC0[4]) = (100:100:100, 100:100:100);
    (FABRIC_CLK => DATA_ADC0[50]) = (100:100:100, 100:100:100);
    (FABRIC_CLK => DATA_ADC0[51]) = (100:100:100, 100:100:100);
    (FABRIC_CLK => DATA_ADC0[52]) = (100:100:100, 100:100:100);
    (FABRIC_CLK => DATA_ADC0[53]) = (100:100:100, 100:100:100);
    (FABRIC_CLK => DATA_ADC0[54]) = (100:100:100, 100:100:100);
    (FABRIC_CLK => DATA_ADC0[55]) = (100:100:100, 100:100:100);
    (FABRIC_CLK => DATA_ADC0[56]) = (100:100:100, 100:100:100);
    (FABRIC_CLK => DATA_ADC0[57]) = (100:100:100, 100:100:100);
    (FABRIC_CLK => DATA_ADC0[58]) = (100:100:100, 100:100:100);
    (FABRIC_CLK => DATA_ADC0[59]) = (100:100:100, 100:100:100);
    (FABRIC_CLK => DATA_ADC0[5]) = (100:100:100, 100:100:100);
    (FABRIC_CLK => DATA_ADC0[60]) = (100:100:100, 100:100:100);
    (FABRIC_CLK => DATA_ADC0[61]) = (100:100:100, 100:100:100);
    (FABRIC_CLK => DATA_ADC0[62]) = (100:100:100, 100:100:100);
    (FABRIC_CLK => DATA_ADC0[63]) = (100:100:100, 100:100:100);
    (FABRIC_CLK => DATA_ADC0[64]) = (100:100:100, 100:100:100);
    (FABRIC_CLK => DATA_ADC0[65]) = (100:100:100, 100:100:100);
    (FABRIC_CLK => DATA_ADC0[66]) = (100:100:100, 100:100:100);
    (FABRIC_CLK => DATA_ADC0[67]) = (100:100:100, 100:100:100);
    (FABRIC_CLK => DATA_ADC0[68]) = (100:100:100, 100:100:100);
    (FABRIC_CLK => DATA_ADC0[69]) = (100:100:100, 100:100:100);
    (FABRIC_CLK => DATA_ADC0[6]) = (100:100:100, 100:100:100);
    (FABRIC_CLK => DATA_ADC0[70]) = (100:100:100, 100:100:100);
    (FABRIC_CLK => DATA_ADC0[71]) = (100:100:100, 100:100:100);
    (FABRIC_CLK => DATA_ADC0[72]) = (100:100:100, 100:100:100);
    (FABRIC_CLK => DATA_ADC0[73]) = (100:100:100, 100:100:100);
    (FABRIC_CLK => DATA_ADC0[74]) = (100:100:100, 100:100:100);
    (FABRIC_CLK => DATA_ADC0[75]) = (100:100:100, 100:100:100);
    (FABRIC_CLK => DATA_ADC0[76]) = (100:100:100, 100:100:100);
    (FABRIC_CLK => DATA_ADC0[77]) = (100:100:100, 100:100:100);
    (FABRIC_CLK => DATA_ADC0[78]) = (100:100:100, 100:100:100);
    (FABRIC_CLK => DATA_ADC0[79]) = (100:100:100, 100:100:100);
    (FABRIC_CLK => DATA_ADC0[7]) = (100:100:100, 100:100:100);
    (FABRIC_CLK => DATA_ADC0[80]) = (100:100:100, 100:100:100);
    (FABRIC_CLK => DATA_ADC0[81]) = (100:100:100, 100:100:100);
    (FABRIC_CLK => DATA_ADC0[82]) = (100:100:100, 100:100:100);
    (FABRIC_CLK => DATA_ADC0[83]) = (100:100:100, 100:100:100);
    (FABRIC_CLK => DATA_ADC0[84]) = (100:100:100, 100:100:100);
    (FABRIC_CLK => DATA_ADC0[85]) = (100:100:100, 100:100:100);
    (FABRIC_CLK => DATA_ADC0[86]) = (100:100:100, 100:100:100);
    (FABRIC_CLK => DATA_ADC0[87]) = (100:100:100, 100:100:100);
    (FABRIC_CLK => DATA_ADC0[88]) = (100:100:100, 100:100:100);
    (FABRIC_CLK => DATA_ADC0[89]) = (100:100:100, 100:100:100);
    (FABRIC_CLK => DATA_ADC0[8]) = (100:100:100, 100:100:100);
    (FABRIC_CLK => DATA_ADC0[90]) = (100:100:100, 100:100:100);
    (FABRIC_CLK => DATA_ADC0[91]) = (100:100:100, 100:100:100);
    (FABRIC_CLK => DATA_ADC0[92]) = (100:100:100, 100:100:100);
    (FABRIC_CLK => DATA_ADC0[93]) = (100:100:100, 100:100:100);
    (FABRIC_CLK => DATA_ADC0[94]) = (100:100:100, 100:100:100);
    (FABRIC_CLK => DATA_ADC0[95]) = (100:100:100, 100:100:100);
    (FABRIC_CLK => DATA_ADC0[96]) = (100:100:100, 100:100:100);
    (FABRIC_CLK => DATA_ADC0[97]) = (100:100:100, 100:100:100);
    (FABRIC_CLK => DATA_ADC0[98]) = (100:100:100, 100:100:100);
    (FABRIC_CLK => DATA_ADC0[99]) = (100:100:100, 100:100:100);
    (FABRIC_CLK => DATA_ADC0[9]) = (100:100:100, 100:100:100);
    (FABRIC_CLK => DATA_ADC1[0]) = (100:100:100, 100:100:100);
    (FABRIC_CLK => DATA_ADC1[100]) = (100:100:100, 100:100:100);
    (FABRIC_CLK => DATA_ADC1[101]) = (100:100:100, 100:100:100);
    (FABRIC_CLK => DATA_ADC1[102]) = (100:100:100, 100:100:100);
    (FABRIC_CLK => DATA_ADC1[103]) = (100:100:100, 100:100:100);
    (FABRIC_CLK => DATA_ADC1[104]) = (100:100:100, 100:100:100);
    (FABRIC_CLK => DATA_ADC1[105]) = (100:100:100, 100:100:100);
    (FABRIC_CLK => DATA_ADC1[106]) = (100:100:100, 100:100:100);
    (FABRIC_CLK => DATA_ADC1[107]) = (100:100:100, 100:100:100);
    (FABRIC_CLK => DATA_ADC1[108]) = (100:100:100, 100:100:100);
    (FABRIC_CLK => DATA_ADC1[109]) = (100:100:100, 100:100:100);
    (FABRIC_CLK => DATA_ADC1[10]) = (100:100:100, 100:100:100);
    (FABRIC_CLK => DATA_ADC1[110]) = (100:100:100, 100:100:100);
    (FABRIC_CLK => DATA_ADC1[111]) = (100:100:100, 100:100:100);
    (FABRIC_CLK => DATA_ADC1[112]) = (100:100:100, 100:100:100);
    (FABRIC_CLK => DATA_ADC1[113]) = (100:100:100, 100:100:100);
    (FABRIC_CLK => DATA_ADC1[114]) = (100:100:100, 100:100:100);
    (FABRIC_CLK => DATA_ADC1[115]) = (100:100:100, 100:100:100);
    (FABRIC_CLK => DATA_ADC1[116]) = (100:100:100, 100:100:100);
    (FABRIC_CLK => DATA_ADC1[117]) = (100:100:100, 100:100:100);
    (FABRIC_CLK => DATA_ADC1[118]) = (100:100:100, 100:100:100);
    (FABRIC_CLK => DATA_ADC1[119]) = (100:100:100, 100:100:100);
    (FABRIC_CLK => DATA_ADC1[11]) = (100:100:100, 100:100:100);
    (FABRIC_CLK => DATA_ADC1[120]) = (100:100:100, 100:100:100);
    (FABRIC_CLK => DATA_ADC1[121]) = (100:100:100, 100:100:100);
    (FABRIC_CLK => DATA_ADC1[122]) = (100:100:100, 100:100:100);
    (FABRIC_CLK => DATA_ADC1[123]) = (100:100:100, 100:100:100);
    (FABRIC_CLK => DATA_ADC1[124]) = (100:100:100, 100:100:100);
    (FABRIC_CLK => DATA_ADC1[125]) = (100:100:100, 100:100:100);
    (FABRIC_CLK => DATA_ADC1[126]) = (100:100:100, 100:100:100);
    (FABRIC_CLK => DATA_ADC1[127]) = (100:100:100, 100:100:100);
    (FABRIC_CLK => DATA_ADC1[128]) = (100:100:100, 100:100:100);
    (FABRIC_CLK => DATA_ADC1[129]) = (100:100:100, 100:100:100);
    (FABRIC_CLK => DATA_ADC1[12]) = (100:100:100, 100:100:100);
    (FABRIC_CLK => DATA_ADC1[130]) = (100:100:100, 100:100:100);
    (FABRIC_CLK => DATA_ADC1[131]) = (100:100:100, 100:100:100);
    (FABRIC_CLK => DATA_ADC1[132]) = (100:100:100, 100:100:100);
    (FABRIC_CLK => DATA_ADC1[133]) = (100:100:100, 100:100:100);
    (FABRIC_CLK => DATA_ADC1[134]) = (100:100:100, 100:100:100);
    (FABRIC_CLK => DATA_ADC1[135]) = (100:100:100, 100:100:100);
    (FABRIC_CLK => DATA_ADC1[136]) = (100:100:100, 100:100:100);
    (FABRIC_CLK => DATA_ADC1[137]) = (100:100:100, 100:100:100);
    (FABRIC_CLK => DATA_ADC1[138]) = (100:100:100, 100:100:100);
    (FABRIC_CLK => DATA_ADC1[139]) = (100:100:100, 100:100:100);
    (FABRIC_CLK => DATA_ADC1[13]) = (100:100:100, 100:100:100);
    (FABRIC_CLK => DATA_ADC1[140]) = (100:100:100, 100:100:100);
    (FABRIC_CLK => DATA_ADC1[141]) = (100:100:100, 100:100:100);
    (FABRIC_CLK => DATA_ADC1[142]) = (100:100:100, 100:100:100);
    (FABRIC_CLK => DATA_ADC1[143]) = (100:100:100, 100:100:100);
    (FABRIC_CLK => DATA_ADC1[144]) = (100:100:100, 100:100:100);
    (FABRIC_CLK => DATA_ADC1[145]) = (100:100:100, 100:100:100);
    (FABRIC_CLK => DATA_ADC1[146]) = (100:100:100, 100:100:100);
    (FABRIC_CLK => DATA_ADC1[147]) = (100:100:100, 100:100:100);
    (FABRIC_CLK => DATA_ADC1[148]) = (100:100:100, 100:100:100);
    (FABRIC_CLK => DATA_ADC1[149]) = (100:100:100, 100:100:100);
    (FABRIC_CLK => DATA_ADC1[14]) = (100:100:100, 100:100:100);
    (FABRIC_CLK => DATA_ADC1[150]) = (100:100:100, 100:100:100);
    (FABRIC_CLK => DATA_ADC1[151]) = (100:100:100, 100:100:100);
    (FABRIC_CLK => DATA_ADC1[152]) = (100:100:100, 100:100:100);
    (FABRIC_CLK => DATA_ADC1[153]) = (100:100:100, 100:100:100);
    (FABRIC_CLK => DATA_ADC1[154]) = (100:100:100, 100:100:100);
    (FABRIC_CLK => DATA_ADC1[155]) = (100:100:100, 100:100:100);
    (FABRIC_CLK => DATA_ADC1[156]) = (100:100:100, 100:100:100);
    (FABRIC_CLK => DATA_ADC1[157]) = (100:100:100, 100:100:100);
    (FABRIC_CLK => DATA_ADC1[158]) = (100:100:100, 100:100:100);
    (FABRIC_CLK => DATA_ADC1[159]) = (100:100:100, 100:100:100);
    (FABRIC_CLK => DATA_ADC1[15]) = (100:100:100, 100:100:100);
    (FABRIC_CLK => DATA_ADC1[160]) = (100:100:100, 100:100:100);
    (FABRIC_CLK => DATA_ADC1[161]) = (100:100:100, 100:100:100);
    (FABRIC_CLK => DATA_ADC1[162]) = (100:100:100, 100:100:100);
    (FABRIC_CLK => DATA_ADC1[163]) = (100:100:100, 100:100:100);
    (FABRIC_CLK => DATA_ADC1[164]) = (100:100:100, 100:100:100);
    (FABRIC_CLK => DATA_ADC1[165]) = (100:100:100, 100:100:100);
    (FABRIC_CLK => DATA_ADC1[166]) = (100:100:100, 100:100:100);
    (FABRIC_CLK => DATA_ADC1[167]) = (100:100:100, 100:100:100);
    (FABRIC_CLK => DATA_ADC1[168]) = (100:100:100, 100:100:100);
    (FABRIC_CLK => DATA_ADC1[169]) = (100:100:100, 100:100:100);
    (FABRIC_CLK => DATA_ADC1[16]) = (100:100:100, 100:100:100);
    (FABRIC_CLK => DATA_ADC1[170]) = (100:100:100, 100:100:100);
    (FABRIC_CLK => DATA_ADC1[171]) = (100:100:100, 100:100:100);
    (FABRIC_CLK => DATA_ADC1[172]) = (100:100:100, 100:100:100);
    (FABRIC_CLK => DATA_ADC1[173]) = (100:100:100, 100:100:100);
    (FABRIC_CLK => DATA_ADC1[174]) = (100:100:100, 100:100:100);
    (FABRIC_CLK => DATA_ADC1[175]) = (100:100:100, 100:100:100);
    (FABRIC_CLK => DATA_ADC1[176]) = (100:100:100, 100:100:100);
    (FABRIC_CLK => DATA_ADC1[177]) = (100:100:100, 100:100:100);
    (FABRIC_CLK => DATA_ADC1[178]) = (100:100:100, 100:100:100);
    (FABRIC_CLK => DATA_ADC1[179]) = (100:100:100, 100:100:100);
    (FABRIC_CLK => DATA_ADC1[17]) = (100:100:100, 100:100:100);
    (FABRIC_CLK => DATA_ADC1[180]) = (100:100:100, 100:100:100);
    (FABRIC_CLK => DATA_ADC1[181]) = (100:100:100, 100:100:100);
    (FABRIC_CLK => DATA_ADC1[182]) = (100:100:100, 100:100:100);
    (FABRIC_CLK => DATA_ADC1[183]) = (100:100:100, 100:100:100);
    (FABRIC_CLK => DATA_ADC1[184]) = (100:100:100, 100:100:100);
    (FABRIC_CLK => DATA_ADC1[185]) = (100:100:100, 100:100:100);
    (FABRIC_CLK => DATA_ADC1[186]) = (100:100:100, 100:100:100);
    (FABRIC_CLK => DATA_ADC1[187]) = (100:100:100, 100:100:100);
    (FABRIC_CLK => DATA_ADC1[188]) = (100:100:100, 100:100:100);
    (FABRIC_CLK => DATA_ADC1[189]) = (100:100:100, 100:100:100);
    (FABRIC_CLK => DATA_ADC1[18]) = (100:100:100, 100:100:100);
    (FABRIC_CLK => DATA_ADC1[190]) = (100:100:100, 100:100:100);
    (FABRIC_CLK => DATA_ADC1[191]) = (100:100:100, 100:100:100);
    (FABRIC_CLK => DATA_ADC1[19]) = (100:100:100, 100:100:100);
    (FABRIC_CLK => DATA_ADC1[1]) = (100:100:100, 100:100:100);
    (FABRIC_CLK => DATA_ADC1[20]) = (100:100:100, 100:100:100);
    (FABRIC_CLK => DATA_ADC1[21]) = (100:100:100, 100:100:100);
    (FABRIC_CLK => DATA_ADC1[22]) = (100:100:100, 100:100:100);
    (FABRIC_CLK => DATA_ADC1[23]) = (100:100:100, 100:100:100);
    (FABRIC_CLK => DATA_ADC1[24]) = (100:100:100, 100:100:100);
    (FABRIC_CLK => DATA_ADC1[25]) = (100:100:100, 100:100:100);
    (FABRIC_CLK => DATA_ADC1[26]) = (100:100:100, 100:100:100);
    (FABRIC_CLK => DATA_ADC1[27]) = (100:100:100, 100:100:100);
    (FABRIC_CLK => DATA_ADC1[28]) = (100:100:100, 100:100:100);
    (FABRIC_CLK => DATA_ADC1[29]) = (100:100:100, 100:100:100);
    (FABRIC_CLK => DATA_ADC1[2]) = (100:100:100, 100:100:100);
    (FABRIC_CLK => DATA_ADC1[30]) = (100:100:100, 100:100:100);
    (FABRIC_CLK => DATA_ADC1[31]) = (100:100:100, 100:100:100);
    (FABRIC_CLK => DATA_ADC1[32]) = (100:100:100, 100:100:100);
    (FABRIC_CLK => DATA_ADC1[33]) = (100:100:100, 100:100:100);
    (FABRIC_CLK => DATA_ADC1[34]) = (100:100:100, 100:100:100);
    (FABRIC_CLK => DATA_ADC1[35]) = (100:100:100, 100:100:100);
    (FABRIC_CLK => DATA_ADC1[36]) = (100:100:100, 100:100:100);
    (FABRIC_CLK => DATA_ADC1[37]) = (100:100:100, 100:100:100);
    (FABRIC_CLK => DATA_ADC1[38]) = (100:100:100, 100:100:100);
    (FABRIC_CLK => DATA_ADC1[39]) = (100:100:100, 100:100:100);
    (FABRIC_CLK => DATA_ADC1[3]) = (100:100:100, 100:100:100);
    (FABRIC_CLK => DATA_ADC1[40]) = (100:100:100, 100:100:100);
    (FABRIC_CLK => DATA_ADC1[41]) = (100:100:100, 100:100:100);
    (FABRIC_CLK => DATA_ADC1[42]) = (100:100:100, 100:100:100);
    (FABRIC_CLK => DATA_ADC1[43]) = (100:100:100, 100:100:100);
    (FABRIC_CLK => DATA_ADC1[44]) = (100:100:100, 100:100:100);
    (FABRIC_CLK => DATA_ADC1[45]) = (100:100:100, 100:100:100);
    (FABRIC_CLK => DATA_ADC1[46]) = (100:100:100, 100:100:100);
    (FABRIC_CLK => DATA_ADC1[47]) = (100:100:100, 100:100:100);
    (FABRIC_CLK => DATA_ADC1[48]) = (100:100:100, 100:100:100);
    (FABRIC_CLK => DATA_ADC1[49]) = (100:100:100, 100:100:100);
    (FABRIC_CLK => DATA_ADC1[4]) = (100:100:100, 100:100:100);
    (FABRIC_CLK => DATA_ADC1[50]) = (100:100:100, 100:100:100);
    (FABRIC_CLK => DATA_ADC1[51]) = (100:100:100, 100:100:100);
    (FABRIC_CLK => DATA_ADC1[52]) = (100:100:100, 100:100:100);
    (FABRIC_CLK => DATA_ADC1[53]) = (100:100:100, 100:100:100);
    (FABRIC_CLK => DATA_ADC1[54]) = (100:100:100, 100:100:100);
    (FABRIC_CLK => DATA_ADC1[55]) = (100:100:100, 100:100:100);
    (FABRIC_CLK => DATA_ADC1[56]) = (100:100:100, 100:100:100);
    (FABRIC_CLK => DATA_ADC1[57]) = (100:100:100, 100:100:100);
    (FABRIC_CLK => DATA_ADC1[58]) = (100:100:100, 100:100:100);
    (FABRIC_CLK => DATA_ADC1[59]) = (100:100:100, 100:100:100);
    (FABRIC_CLK => DATA_ADC1[5]) = (100:100:100, 100:100:100);
    (FABRIC_CLK => DATA_ADC1[60]) = (100:100:100, 100:100:100);
    (FABRIC_CLK => DATA_ADC1[61]) = (100:100:100, 100:100:100);
    (FABRIC_CLK => DATA_ADC1[62]) = (100:100:100, 100:100:100);
    (FABRIC_CLK => DATA_ADC1[63]) = (100:100:100, 100:100:100);
    (FABRIC_CLK => DATA_ADC1[64]) = (100:100:100, 100:100:100);
    (FABRIC_CLK => DATA_ADC1[65]) = (100:100:100, 100:100:100);
    (FABRIC_CLK => DATA_ADC1[66]) = (100:100:100, 100:100:100);
    (FABRIC_CLK => DATA_ADC1[67]) = (100:100:100, 100:100:100);
    (FABRIC_CLK => DATA_ADC1[68]) = (100:100:100, 100:100:100);
    (FABRIC_CLK => DATA_ADC1[69]) = (100:100:100, 100:100:100);
    (FABRIC_CLK => DATA_ADC1[6]) = (100:100:100, 100:100:100);
    (FABRIC_CLK => DATA_ADC1[70]) = (100:100:100, 100:100:100);
    (FABRIC_CLK => DATA_ADC1[71]) = (100:100:100, 100:100:100);
    (FABRIC_CLK => DATA_ADC1[72]) = (100:100:100, 100:100:100);
    (FABRIC_CLK => DATA_ADC1[73]) = (100:100:100, 100:100:100);
    (FABRIC_CLK => DATA_ADC1[74]) = (100:100:100, 100:100:100);
    (FABRIC_CLK => DATA_ADC1[75]) = (100:100:100, 100:100:100);
    (FABRIC_CLK => DATA_ADC1[76]) = (100:100:100, 100:100:100);
    (FABRIC_CLK => DATA_ADC1[77]) = (100:100:100, 100:100:100);
    (FABRIC_CLK => DATA_ADC1[78]) = (100:100:100, 100:100:100);
    (FABRIC_CLK => DATA_ADC1[79]) = (100:100:100, 100:100:100);
    (FABRIC_CLK => DATA_ADC1[7]) = (100:100:100, 100:100:100);
    (FABRIC_CLK => DATA_ADC1[80]) = (100:100:100, 100:100:100);
    (FABRIC_CLK => DATA_ADC1[81]) = (100:100:100, 100:100:100);
    (FABRIC_CLK => DATA_ADC1[82]) = (100:100:100, 100:100:100);
    (FABRIC_CLK => DATA_ADC1[83]) = (100:100:100, 100:100:100);
    (FABRIC_CLK => DATA_ADC1[84]) = (100:100:100, 100:100:100);
    (FABRIC_CLK => DATA_ADC1[85]) = (100:100:100, 100:100:100);
    (FABRIC_CLK => DATA_ADC1[86]) = (100:100:100, 100:100:100);
    (FABRIC_CLK => DATA_ADC1[87]) = (100:100:100, 100:100:100);
    (FABRIC_CLK => DATA_ADC1[88]) = (100:100:100, 100:100:100);
    (FABRIC_CLK => DATA_ADC1[89]) = (100:100:100, 100:100:100);
    (FABRIC_CLK => DATA_ADC1[8]) = (100:100:100, 100:100:100);
    (FABRIC_CLK => DATA_ADC1[90]) = (100:100:100, 100:100:100);
    (FABRIC_CLK => DATA_ADC1[91]) = (100:100:100, 100:100:100);
    (FABRIC_CLK => DATA_ADC1[92]) = (100:100:100, 100:100:100);
    (FABRIC_CLK => DATA_ADC1[93]) = (100:100:100, 100:100:100);
    (FABRIC_CLK => DATA_ADC1[94]) = (100:100:100, 100:100:100);
    (FABRIC_CLK => DATA_ADC1[95]) = (100:100:100, 100:100:100);
    (FABRIC_CLK => DATA_ADC1[96]) = (100:100:100, 100:100:100);
    (FABRIC_CLK => DATA_ADC1[97]) = (100:100:100, 100:100:100);
    (FABRIC_CLK => DATA_ADC1[98]) = (100:100:100, 100:100:100);
    (FABRIC_CLK => DATA_ADC1[99]) = (100:100:100, 100:100:100);
    (FABRIC_CLK => DATA_ADC1[9]) = (100:100:100, 100:100:100);
    (FABRIC_CLK => DATA_ADC2[0]) = (100:100:100, 100:100:100);
    (FABRIC_CLK => DATA_ADC2[100]) = (100:100:100, 100:100:100);
    (FABRIC_CLK => DATA_ADC2[101]) = (100:100:100, 100:100:100);
    (FABRIC_CLK => DATA_ADC2[102]) = (100:100:100, 100:100:100);
    (FABRIC_CLK => DATA_ADC2[103]) = (100:100:100, 100:100:100);
    (FABRIC_CLK => DATA_ADC2[104]) = (100:100:100, 100:100:100);
    (FABRIC_CLK => DATA_ADC2[105]) = (100:100:100, 100:100:100);
    (FABRIC_CLK => DATA_ADC2[106]) = (100:100:100, 100:100:100);
    (FABRIC_CLK => DATA_ADC2[107]) = (100:100:100, 100:100:100);
    (FABRIC_CLK => DATA_ADC2[108]) = (100:100:100, 100:100:100);
    (FABRIC_CLK => DATA_ADC2[109]) = (100:100:100, 100:100:100);
    (FABRIC_CLK => DATA_ADC2[10]) = (100:100:100, 100:100:100);
    (FABRIC_CLK => DATA_ADC2[110]) = (100:100:100, 100:100:100);
    (FABRIC_CLK => DATA_ADC2[111]) = (100:100:100, 100:100:100);
    (FABRIC_CLK => DATA_ADC2[112]) = (100:100:100, 100:100:100);
    (FABRIC_CLK => DATA_ADC2[113]) = (100:100:100, 100:100:100);
    (FABRIC_CLK => DATA_ADC2[114]) = (100:100:100, 100:100:100);
    (FABRIC_CLK => DATA_ADC2[115]) = (100:100:100, 100:100:100);
    (FABRIC_CLK => DATA_ADC2[116]) = (100:100:100, 100:100:100);
    (FABRIC_CLK => DATA_ADC2[117]) = (100:100:100, 100:100:100);
    (FABRIC_CLK => DATA_ADC2[118]) = (100:100:100, 100:100:100);
    (FABRIC_CLK => DATA_ADC2[119]) = (100:100:100, 100:100:100);
    (FABRIC_CLK => DATA_ADC2[11]) = (100:100:100, 100:100:100);
    (FABRIC_CLK => DATA_ADC2[120]) = (100:100:100, 100:100:100);
    (FABRIC_CLK => DATA_ADC2[121]) = (100:100:100, 100:100:100);
    (FABRIC_CLK => DATA_ADC2[122]) = (100:100:100, 100:100:100);
    (FABRIC_CLK => DATA_ADC2[123]) = (100:100:100, 100:100:100);
    (FABRIC_CLK => DATA_ADC2[124]) = (100:100:100, 100:100:100);
    (FABRIC_CLK => DATA_ADC2[125]) = (100:100:100, 100:100:100);
    (FABRIC_CLK => DATA_ADC2[126]) = (100:100:100, 100:100:100);
    (FABRIC_CLK => DATA_ADC2[127]) = (100:100:100, 100:100:100);
    (FABRIC_CLK => DATA_ADC2[128]) = (100:100:100, 100:100:100);
    (FABRIC_CLK => DATA_ADC2[129]) = (100:100:100, 100:100:100);
    (FABRIC_CLK => DATA_ADC2[12]) = (100:100:100, 100:100:100);
    (FABRIC_CLK => DATA_ADC2[130]) = (100:100:100, 100:100:100);
    (FABRIC_CLK => DATA_ADC2[131]) = (100:100:100, 100:100:100);
    (FABRIC_CLK => DATA_ADC2[132]) = (100:100:100, 100:100:100);
    (FABRIC_CLK => DATA_ADC2[133]) = (100:100:100, 100:100:100);
    (FABRIC_CLK => DATA_ADC2[134]) = (100:100:100, 100:100:100);
    (FABRIC_CLK => DATA_ADC2[135]) = (100:100:100, 100:100:100);
    (FABRIC_CLK => DATA_ADC2[136]) = (100:100:100, 100:100:100);
    (FABRIC_CLK => DATA_ADC2[137]) = (100:100:100, 100:100:100);
    (FABRIC_CLK => DATA_ADC2[138]) = (100:100:100, 100:100:100);
    (FABRIC_CLK => DATA_ADC2[139]) = (100:100:100, 100:100:100);
    (FABRIC_CLK => DATA_ADC2[13]) = (100:100:100, 100:100:100);
    (FABRIC_CLK => DATA_ADC2[140]) = (100:100:100, 100:100:100);
    (FABRIC_CLK => DATA_ADC2[141]) = (100:100:100, 100:100:100);
    (FABRIC_CLK => DATA_ADC2[142]) = (100:100:100, 100:100:100);
    (FABRIC_CLK => DATA_ADC2[143]) = (100:100:100, 100:100:100);
    (FABRIC_CLK => DATA_ADC2[144]) = (100:100:100, 100:100:100);
    (FABRIC_CLK => DATA_ADC2[145]) = (100:100:100, 100:100:100);
    (FABRIC_CLK => DATA_ADC2[146]) = (100:100:100, 100:100:100);
    (FABRIC_CLK => DATA_ADC2[147]) = (100:100:100, 100:100:100);
    (FABRIC_CLK => DATA_ADC2[148]) = (100:100:100, 100:100:100);
    (FABRIC_CLK => DATA_ADC2[149]) = (100:100:100, 100:100:100);
    (FABRIC_CLK => DATA_ADC2[14]) = (100:100:100, 100:100:100);
    (FABRIC_CLK => DATA_ADC2[150]) = (100:100:100, 100:100:100);
    (FABRIC_CLK => DATA_ADC2[151]) = (100:100:100, 100:100:100);
    (FABRIC_CLK => DATA_ADC2[152]) = (100:100:100, 100:100:100);
    (FABRIC_CLK => DATA_ADC2[153]) = (100:100:100, 100:100:100);
    (FABRIC_CLK => DATA_ADC2[154]) = (100:100:100, 100:100:100);
    (FABRIC_CLK => DATA_ADC2[155]) = (100:100:100, 100:100:100);
    (FABRIC_CLK => DATA_ADC2[156]) = (100:100:100, 100:100:100);
    (FABRIC_CLK => DATA_ADC2[157]) = (100:100:100, 100:100:100);
    (FABRIC_CLK => DATA_ADC2[158]) = (100:100:100, 100:100:100);
    (FABRIC_CLK => DATA_ADC2[159]) = (100:100:100, 100:100:100);
    (FABRIC_CLK => DATA_ADC2[15]) = (100:100:100, 100:100:100);
    (FABRIC_CLK => DATA_ADC2[160]) = (100:100:100, 100:100:100);
    (FABRIC_CLK => DATA_ADC2[161]) = (100:100:100, 100:100:100);
    (FABRIC_CLK => DATA_ADC2[162]) = (100:100:100, 100:100:100);
    (FABRIC_CLK => DATA_ADC2[163]) = (100:100:100, 100:100:100);
    (FABRIC_CLK => DATA_ADC2[164]) = (100:100:100, 100:100:100);
    (FABRIC_CLK => DATA_ADC2[165]) = (100:100:100, 100:100:100);
    (FABRIC_CLK => DATA_ADC2[166]) = (100:100:100, 100:100:100);
    (FABRIC_CLK => DATA_ADC2[167]) = (100:100:100, 100:100:100);
    (FABRIC_CLK => DATA_ADC2[168]) = (100:100:100, 100:100:100);
    (FABRIC_CLK => DATA_ADC2[169]) = (100:100:100, 100:100:100);
    (FABRIC_CLK => DATA_ADC2[16]) = (100:100:100, 100:100:100);
    (FABRIC_CLK => DATA_ADC2[170]) = (100:100:100, 100:100:100);
    (FABRIC_CLK => DATA_ADC2[171]) = (100:100:100, 100:100:100);
    (FABRIC_CLK => DATA_ADC2[172]) = (100:100:100, 100:100:100);
    (FABRIC_CLK => DATA_ADC2[173]) = (100:100:100, 100:100:100);
    (FABRIC_CLK => DATA_ADC2[174]) = (100:100:100, 100:100:100);
    (FABRIC_CLK => DATA_ADC2[175]) = (100:100:100, 100:100:100);
    (FABRIC_CLK => DATA_ADC2[176]) = (100:100:100, 100:100:100);
    (FABRIC_CLK => DATA_ADC2[177]) = (100:100:100, 100:100:100);
    (FABRIC_CLK => DATA_ADC2[178]) = (100:100:100, 100:100:100);
    (FABRIC_CLK => DATA_ADC2[179]) = (100:100:100, 100:100:100);
    (FABRIC_CLK => DATA_ADC2[17]) = (100:100:100, 100:100:100);
    (FABRIC_CLK => DATA_ADC2[180]) = (100:100:100, 100:100:100);
    (FABRIC_CLK => DATA_ADC2[181]) = (100:100:100, 100:100:100);
    (FABRIC_CLK => DATA_ADC2[182]) = (100:100:100, 100:100:100);
    (FABRIC_CLK => DATA_ADC2[183]) = (100:100:100, 100:100:100);
    (FABRIC_CLK => DATA_ADC2[184]) = (100:100:100, 100:100:100);
    (FABRIC_CLK => DATA_ADC2[185]) = (100:100:100, 100:100:100);
    (FABRIC_CLK => DATA_ADC2[186]) = (100:100:100, 100:100:100);
    (FABRIC_CLK => DATA_ADC2[187]) = (100:100:100, 100:100:100);
    (FABRIC_CLK => DATA_ADC2[188]) = (100:100:100, 100:100:100);
    (FABRIC_CLK => DATA_ADC2[189]) = (100:100:100, 100:100:100);
    (FABRIC_CLK => DATA_ADC2[18]) = (100:100:100, 100:100:100);
    (FABRIC_CLK => DATA_ADC2[190]) = (100:100:100, 100:100:100);
    (FABRIC_CLK => DATA_ADC2[191]) = (100:100:100, 100:100:100);
    (FABRIC_CLK => DATA_ADC2[19]) = (100:100:100, 100:100:100);
    (FABRIC_CLK => DATA_ADC2[1]) = (100:100:100, 100:100:100);
    (FABRIC_CLK => DATA_ADC2[20]) = (100:100:100, 100:100:100);
    (FABRIC_CLK => DATA_ADC2[21]) = (100:100:100, 100:100:100);
    (FABRIC_CLK => DATA_ADC2[22]) = (100:100:100, 100:100:100);
    (FABRIC_CLK => DATA_ADC2[23]) = (100:100:100, 100:100:100);
    (FABRIC_CLK => DATA_ADC2[24]) = (100:100:100, 100:100:100);
    (FABRIC_CLK => DATA_ADC2[25]) = (100:100:100, 100:100:100);
    (FABRIC_CLK => DATA_ADC2[26]) = (100:100:100, 100:100:100);
    (FABRIC_CLK => DATA_ADC2[27]) = (100:100:100, 100:100:100);
    (FABRIC_CLK => DATA_ADC2[28]) = (100:100:100, 100:100:100);
    (FABRIC_CLK => DATA_ADC2[29]) = (100:100:100, 100:100:100);
    (FABRIC_CLK => DATA_ADC2[2]) = (100:100:100, 100:100:100);
    (FABRIC_CLK => DATA_ADC2[30]) = (100:100:100, 100:100:100);
    (FABRIC_CLK => DATA_ADC2[31]) = (100:100:100, 100:100:100);
    (FABRIC_CLK => DATA_ADC2[32]) = (100:100:100, 100:100:100);
    (FABRIC_CLK => DATA_ADC2[33]) = (100:100:100, 100:100:100);
    (FABRIC_CLK => DATA_ADC2[34]) = (100:100:100, 100:100:100);
    (FABRIC_CLK => DATA_ADC2[35]) = (100:100:100, 100:100:100);
    (FABRIC_CLK => DATA_ADC2[36]) = (100:100:100, 100:100:100);
    (FABRIC_CLK => DATA_ADC2[37]) = (100:100:100, 100:100:100);
    (FABRIC_CLK => DATA_ADC2[38]) = (100:100:100, 100:100:100);
    (FABRIC_CLK => DATA_ADC2[39]) = (100:100:100, 100:100:100);
    (FABRIC_CLK => DATA_ADC2[3]) = (100:100:100, 100:100:100);
    (FABRIC_CLK => DATA_ADC2[40]) = (100:100:100, 100:100:100);
    (FABRIC_CLK => DATA_ADC2[41]) = (100:100:100, 100:100:100);
    (FABRIC_CLK => DATA_ADC2[42]) = (100:100:100, 100:100:100);
    (FABRIC_CLK => DATA_ADC2[43]) = (100:100:100, 100:100:100);
    (FABRIC_CLK => DATA_ADC2[44]) = (100:100:100, 100:100:100);
    (FABRIC_CLK => DATA_ADC2[45]) = (100:100:100, 100:100:100);
    (FABRIC_CLK => DATA_ADC2[46]) = (100:100:100, 100:100:100);
    (FABRIC_CLK => DATA_ADC2[47]) = (100:100:100, 100:100:100);
    (FABRIC_CLK => DATA_ADC2[48]) = (100:100:100, 100:100:100);
    (FABRIC_CLK => DATA_ADC2[49]) = (100:100:100, 100:100:100);
    (FABRIC_CLK => DATA_ADC2[4]) = (100:100:100, 100:100:100);
    (FABRIC_CLK => DATA_ADC2[50]) = (100:100:100, 100:100:100);
    (FABRIC_CLK => DATA_ADC2[51]) = (100:100:100, 100:100:100);
    (FABRIC_CLK => DATA_ADC2[52]) = (100:100:100, 100:100:100);
    (FABRIC_CLK => DATA_ADC2[53]) = (100:100:100, 100:100:100);
    (FABRIC_CLK => DATA_ADC2[54]) = (100:100:100, 100:100:100);
    (FABRIC_CLK => DATA_ADC2[55]) = (100:100:100, 100:100:100);
    (FABRIC_CLK => DATA_ADC2[56]) = (100:100:100, 100:100:100);
    (FABRIC_CLK => DATA_ADC2[57]) = (100:100:100, 100:100:100);
    (FABRIC_CLK => DATA_ADC2[58]) = (100:100:100, 100:100:100);
    (FABRIC_CLK => DATA_ADC2[59]) = (100:100:100, 100:100:100);
    (FABRIC_CLK => DATA_ADC2[5]) = (100:100:100, 100:100:100);
    (FABRIC_CLK => DATA_ADC2[60]) = (100:100:100, 100:100:100);
    (FABRIC_CLK => DATA_ADC2[61]) = (100:100:100, 100:100:100);
    (FABRIC_CLK => DATA_ADC2[62]) = (100:100:100, 100:100:100);
    (FABRIC_CLK => DATA_ADC2[63]) = (100:100:100, 100:100:100);
    (FABRIC_CLK => DATA_ADC2[64]) = (100:100:100, 100:100:100);
    (FABRIC_CLK => DATA_ADC2[65]) = (100:100:100, 100:100:100);
    (FABRIC_CLK => DATA_ADC2[66]) = (100:100:100, 100:100:100);
    (FABRIC_CLK => DATA_ADC2[67]) = (100:100:100, 100:100:100);
    (FABRIC_CLK => DATA_ADC2[68]) = (100:100:100, 100:100:100);
    (FABRIC_CLK => DATA_ADC2[69]) = (100:100:100, 100:100:100);
    (FABRIC_CLK => DATA_ADC2[6]) = (100:100:100, 100:100:100);
    (FABRIC_CLK => DATA_ADC2[70]) = (100:100:100, 100:100:100);
    (FABRIC_CLK => DATA_ADC2[71]) = (100:100:100, 100:100:100);
    (FABRIC_CLK => DATA_ADC2[72]) = (100:100:100, 100:100:100);
    (FABRIC_CLK => DATA_ADC2[73]) = (100:100:100, 100:100:100);
    (FABRIC_CLK => DATA_ADC2[74]) = (100:100:100, 100:100:100);
    (FABRIC_CLK => DATA_ADC2[75]) = (100:100:100, 100:100:100);
    (FABRIC_CLK => DATA_ADC2[76]) = (100:100:100, 100:100:100);
    (FABRIC_CLK => DATA_ADC2[77]) = (100:100:100, 100:100:100);
    (FABRIC_CLK => DATA_ADC2[78]) = (100:100:100, 100:100:100);
    (FABRIC_CLK => DATA_ADC2[79]) = (100:100:100, 100:100:100);
    (FABRIC_CLK => DATA_ADC2[7]) = (100:100:100, 100:100:100);
    (FABRIC_CLK => DATA_ADC2[80]) = (100:100:100, 100:100:100);
    (FABRIC_CLK => DATA_ADC2[81]) = (100:100:100, 100:100:100);
    (FABRIC_CLK => DATA_ADC2[82]) = (100:100:100, 100:100:100);
    (FABRIC_CLK => DATA_ADC2[83]) = (100:100:100, 100:100:100);
    (FABRIC_CLK => DATA_ADC2[84]) = (100:100:100, 100:100:100);
    (FABRIC_CLK => DATA_ADC2[85]) = (100:100:100, 100:100:100);
    (FABRIC_CLK => DATA_ADC2[86]) = (100:100:100, 100:100:100);
    (FABRIC_CLK => DATA_ADC2[87]) = (100:100:100, 100:100:100);
    (FABRIC_CLK => DATA_ADC2[88]) = (100:100:100, 100:100:100);
    (FABRIC_CLK => DATA_ADC2[89]) = (100:100:100, 100:100:100);
    (FABRIC_CLK => DATA_ADC2[8]) = (100:100:100, 100:100:100);
    (FABRIC_CLK => DATA_ADC2[90]) = (100:100:100, 100:100:100);
    (FABRIC_CLK => DATA_ADC2[91]) = (100:100:100, 100:100:100);
    (FABRIC_CLK => DATA_ADC2[92]) = (100:100:100, 100:100:100);
    (FABRIC_CLK => DATA_ADC2[93]) = (100:100:100, 100:100:100);
    (FABRIC_CLK => DATA_ADC2[94]) = (100:100:100, 100:100:100);
    (FABRIC_CLK => DATA_ADC2[95]) = (100:100:100, 100:100:100);
    (FABRIC_CLK => DATA_ADC2[96]) = (100:100:100, 100:100:100);
    (FABRIC_CLK => DATA_ADC2[97]) = (100:100:100, 100:100:100);
    (FABRIC_CLK => DATA_ADC2[98]) = (100:100:100, 100:100:100);
    (FABRIC_CLK => DATA_ADC2[99]) = (100:100:100, 100:100:100);
    (FABRIC_CLK => DATA_ADC2[9]) = (100:100:100, 100:100:100);
    (FABRIC_CLK => DATA_ADC3[0]) = (100:100:100, 100:100:100);
    (FABRIC_CLK => DATA_ADC3[100]) = (100:100:100, 100:100:100);
    (FABRIC_CLK => DATA_ADC3[101]) = (100:100:100, 100:100:100);
    (FABRIC_CLK => DATA_ADC3[102]) = (100:100:100, 100:100:100);
    (FABRIC_CLK => DATA_ADC3[103]) = (100:100:100, 100:100:100);
    (FABRIC_CLK => DATA_ADC3[104]) = (100:100:100, 100:100:100);
    (FABRIC_CLK => DATA_ADC3[105]) = (100:100:100, 100:100:100);
    (FABRIC_CLK => DATA_ADC3[106]) = (100:100:100, 100:100:100);
    (FABRIC_CLK => DATA_ADC3[107]) = (100:100:100, 100:100:100);
    (FABRIC_CLK => DATA_ADC3[108]) = (100:100:100, 100:100:100);
    (FABRIC_CLK => DATA_ADC3[109]) = (100:100:100, 100:100:100);
    (FABRIC_CLK => DATA_ADC3[10]) = (100:100:100, 100:100:100);
    (FABRIC_CLK => DATA_ADC3[110]) = (100:100:100, 100:100:100);
    (FABRIC_CLK => DATA_ADC3[111]) = (100:100:100, 100:100:100);
    (FABRIC_CLK => DATA_ADC3[112]) = (100:100:100, 100:100:100);
    (FABRIC_CLK => DATA_ADC3[113]) = (100:100:100, 100:100:100);
    (FABRIC_CLK => DATA_ADC3[114]) = (100:100:100, 100:100:100);
    (FABRIC_CLK => DATA_ADC3[115]) = (100:100:100, 100:100:100);
    (FABRIC_CLK => DATA_ADC3[116]) = (100:100:100, 100:100:100);
    (FABRIC_CLK => DATA_ADC3[117]) = (100:100:100, 100:100:100);
    (FABRIC_CLK => DATA_ADC3[118]) = (100:100:100, 100:100:100);
    (FABRIC_CLK => DATA_ADC3[119]) = (100:100:100, 100:100:100);
    (FABRIC_CLK => DATA_ADC3[11]) = (100:100:100, 100:100:100);
    (FABRIC_CLK => DATA_ADC3[120]) = (100:100:100, 100:100:100);
    (FABRIC_CLK => DATA_ADC3[121]) = (100:100:100, 100:100:100);
    (FABRIC_CLK => DATA_ADC3[122]) = (100:100:100, 100:100:100);
    (FABRIC_CLK => DATA_ADC3[123]) = (100:100:100, 100:100:100);
    (FABRIC_CLK => DATA_ADC3[124]) = (100:100:100, 100:100:100);
    (FABRIC_CLK => DATA_ADC3[125]) = (100:100:100, 100:100:100);
    (FABRIC_CLK => DATA_ADC3[126]) = (100:100:100, 100:100:100);
    (FABRIC_CLK => DATA_ADC3[127]) = (100:100:100, 100:100:100);
    (FABRIC_CLK => DATA_ADC3[128]) = (100:100:100, 100:100:100);
    (FABRIC_CLK => DATA_ADC3[129]) = (100:100:100, 100:100:100);
    (FABRIC_CLK => DATA_ADC3[12]) = (100:100:100, 100:100:100);
    (FABRIC_CLK => DATA_ADC3[130]) = (100:100:100, 100:100:100);
    (FABRIC_CLK => DATA_ADC3[131]) = (100:100:100, 100:100:100);
    (FABRIC_CLK => DATA_ADC3[132]) = (100:100:100, 100:100:100);
    (FABRIC_CLK => DATA_ADC3[133]) = (100:100:100, 100:100:100);
    (FABRIC_CLK => DATA_ADC3[134]) = (100:100:100, 100:100:100);
    (FABRIC_CLK => DATA_ADC3[135]) = (100:100:100, 100:100:100);
    (FABRIC_CLK => DATA_ADC3[136]) = (100:100:100, 100:100:100);
    (FABRIC_CLK => DATA_ADC3[137]) = (100:100:100, 100:100:100);
    (FABRIC_CLK => DATA_ADC3[138]) = (100:100:100, 100:100:100);
    (FABRIC_CLK => DATA_ADC3[139]) = (100:100:100, 100:100:100);
    (FABRIC_CLK => DATA_ADC3[13]) = (100:100:100, 100:100:100);
    (FABRIC_CLK => DATA_ADC3[140]) = (100:100:100, 100:100:100);
    (FABRIC_CLK => DATA_ADC3[141]) = (100:100:100, 100:100:100);
    (FABRIC_CLK => DATA_ADC3[142]) = (100:100:100, 100:100:100);
    (FABRIC_CLK => DATA_ADC3[143]) = (100:100:100, 100:100:100);
    (FABRIC_CLK => DATA_ADC3[144]) = (100:100:100, 100:100:100);
    (FABRIC_CLK => DATA_ADC3[145]) = (100:100:100, 100:100:100);
    (FABRIC_CLK => DATA_ADC3[146]) = (100:100:100, 100:100:100);
    (FABRIC_CLK => DATA_ADC3[147]) = (100:100:100, 100:100:100);
    (FABRIC_CLK => DATA_ADC3[148]) = (100:100:100, 100:100:100);
    (FABRIC_CLK => DATA_ADC3[149]) = (100:100:100, 100:100:100);
    (FABRIC_CLK => DATA_ADC3[14]) = (100:100:100, 100:100:100);
    (FABRIC_CLK => DATA_ADC3[150]) = (100:100:100, 100:100:100);
    (FABRIC_CLK => DATA_ADC3[151]) = (100:100:100, 100:100:100);
    (FABRIC_CLK => DATA_ADC3[152]) = (100:100:100, 100:100:100);
    (FABRIC_CLK => DATA_ADC3[153]) = (100:100:100, 100:100:100);
    (FABRIC_CLK => DATA_ADC3[154]) = (100:100:100, 100:100:100);
    (FABRIC_CLK => DATA_ADC3[155]) = (100:100:100, 100:100:100);
    (FABRIC_CLK => DATA_ADC3[156]) = (100:100:100, 100:100:100);
    (FABRIC_CLK => DATA_ADC3[157]) = (100:100:100, 100:100:100);
    (FABRIC_CLK => DATA_ADC3[158]) = (100:100:100, 100:100:100);
    (FABRIC_CLK => DATA_ADC3[159]) = (100:100:100, 100:100:100);
    (FABRIC_CLK => DATA_ADC3[15]) = (100:100:100, 100:100:100);
    (FABRIC_CLK => DATA_ADC3[160]) = (100:100:100, 100:100:100);
    (FABRIC_CLK => DATA_ADC3[161]) = (100:100:100, 100:100:100);
    (FABRIC_CLK => DATA_ADC3[162]) = (100:100:100, 100:100:100);
    (FABRIC_CLK => DATA_ADC3[163]) = (100:100:100, 100:100:100);
    (FABRIC_CLK => DATA_ADC3[164]) = (100:100:100, 100:100:100);
    (FABRIC_CLK => DATA_ADC3[165]) = (100:100:100, 100:100:100);
    (FABRIC_CLK => DATA_ADC3[166]) = (100:100:100, 100:100:100);
    (FABRIC_CLK => DATA_ADC3[167]) = (100:100:100, 100:100:100);
    (FABRIC_CLK => DATA_ADC3[168]) = (100:100:100, 100:100:100);
    (FABRIC_CLK => DATA_ADC3[169]) = (100:100:100, 100:100:100);
    (FABRIC_CLK => DATA_ADC3[16]) = (100:100:100, 100:100:100);
    (FABRIC_CLK => DATA_ADC3[170]) = (100:100:100, 100:100:100);
    (FABRIC_CLK => DATA_ADC3[171]) = (100:100:100, 100:100:100);
    (FABRIC_CLK => DATA_ADC3[172]) = (100:100:100, 100:100:100);
    (FABRIC_CLK => DATA_ADC3[173]) = (100:100:100, 100:100:100);
    (FABRIC_CLK => DATA_ADC3[174]) = (100:100:100, 100:100:100);
    (FABRIC_CLK => DATA_ADC3[175]) = (100:100:100, 100:100:100);
    (FABRIC_CLK => DATA_ADC3[176]) = (100:100:100, 100:100:100);
    (FABRIC_CLK => DATA_ADC3[177]) = (100:100:100, 100:100:100);
    (FABRIC_CLK => DATA_ADC3[178]) = (100:100:100, 100:100:100);
    (FABRIC_CLK => DATA_ADC3[179]) = (100:100:100, 100:100:100);
    (FABRIC_CLK => DATA_ADC3[17]) = (100:100:100, 100:100:100);
    (FABRIC_CLK => DATA_ADC3[180]) = (100:100:100, 100:100:100);
    (FABRIC_CLK => DATA_ADC3[181]) = (100:100:100, 100:100:100);
    (FABRIC_CLK => DATA_ADC3[182]) = (100:100:100, 100:100:100);
    (FABRIC_CLK => DATA_ADC3[183]) = (100:100:100, 100:100:100);
    (FABRIC_CLK => DATA_ADC3[184]) = (100:100:100, 100:100:100);
    (FABRIC_CLK => DATA_ADC3[185]) = (100:100:100, 100:100:100);
    (FABRIC_CLK => DATA_ADC3[186]) = (100:100:100, 100:100:100);
    (FABRIC_CLK => DATA_ADC3[187]) = (100:100:100, 100:100:100);
    (FABRIC_CLK => DATA_ADC3[188]) = (100:100:100, 100:100:100);
    (FABRIC_CLK => DATA_ADC3[189]) = (100:100:100, 100:100:100);
    (FABRIC_CLK => DATA_ADC3[18]) = (100:100:100, 100:100:100);
    (FABRIC_CLK => DATA_ADC3[190]) = (100:100:100, 100:100:100);
    (FABRIC_CLK => DATA_ADC3[191]) = (100:100:100, 100:100:100);
    (FABRIC_CLK => DATA_ADC3[19]) = (100:100:100, 100:100:100);
    (FABRIC_CLK => DATA_ADC3[1]) = (100:100:100, 100:100:100);
    (FABRIC_CLK => DATA_ADC3[20]) = (100:100:100, 100:100:100);
    (FABRIC_CLK => DATA_ADC3[21]) = (100:100:100, 100:100:100);
    (FABRIC_CLK => DATA_ADC3[22]) = (100:100:100, 100:100:100);
    (FABRIC_CLK => DATA_ADC3[23]) = (100:100:100, 100:100:100);
    (FABRIC_CLK => DATA_ADC3[24]) = (100:100:100, 100:100:100);
    (FABRIC_CLK => DATA_ADC3[25]) = (100:100:100, 100:100:100);
    (FABRIC_CLK => DATA_ADC3[26]) = (100:100:100, 100:100:100);
    (FABRIC_CLK => DATA_ADC3[27]) = (100:100:100, 100:100:100);
    (FABRIC_CLK => DATA_ADC3[28]) = (100:100:100, 100:100:100);
    (FABRIC_CLK => DATA_ADC3[29]) = (100:100:100, 100:100:100);
    (FABRIC_CLK => DATA_ADC3[2]) = (100:100:100, 100:100:100);
    (FABRIC_CLK => DATA_ADC3[30]) = (100:100:100, 100:100:100);
    (FABRIC_CLK => DATA_ADC3[31]) = (100:100:100, 100:100:100);
    (FABRIC_CLK => DATA_ADC3[32]) = (100:100:100, 100:100:100);
    (FABRIC_CLK => DATA_ADC3[33]) = (100:100:100, 100:100:100);
    (FABRIC_CLK => DATA_ADC3[34]) = (100:100:100, 100:100:100);
    (FABRIC_CLK => DATA_ADC3[35]) = (100:100:100, 100:100:100);
    (FABRIC_CLK => DATA_ADC3[36]) = (100:100:100, 100:100:100);
    (FABRIC_CLK => DATA_ADC3[37]) = (100:100:100, 100:100:100);
    (FABRIC_CLK => DATA_ADC3[38]) = (100:100:100, 100:100:100);
    (FABRIC_CLK => DATA_ADC3[39]) = (100:100:100, 100:100:100);
    (FABRIC_CLK => DATA_ADC3[3]) = (100:100:100, 100:100:100);
    (FABRIC_CLK => DATA_ADC3[40]) = (100:100:100, 100:100:100);
    (FABRIC_CLK => DATA_ADC3[41]) = (100:100:100, 100:100:100);
    (FABRIC_CLK => DATA_ADC3[42]) = (100:100:100, 100:100:100);
    (FABRIC_CLK => DATA_ADC3[43]) = (100:100:100, 100:100:100);
    (FABRIC_CLK => DATA_ADC3[44]) = (100:100:100, 100:100:100);
    (FABRIC_CLK => DATA_ADC3[45]) = (100:100:100, 100:100:100);
    (FABRIC_CLK => DATA_ADC3[46]) = (100:100:100, 100:100:100);
    (FABRIC_CLK => DATA_ADC3[47]) = (100:100:100, 100:100:100);
    (FABRIC_CLK => DATA_ADC3[48]) = (100:100:100, 100:100:100);
    (FABRIC_CLK => DATA_ADC3[49]) = (100:100:100, 100:100:100);
    (FABRIC_CLK => DATA_ADC3[4]) = (100:100:100, 100:100:100);
    (FABRIC_CLK => DATA_ADC3[50]) = (100:100:100, 100:100:100);
    (FABRIC_CLK => DATA_ADC3[51]) = (100:100:100, 100:100:100);
    (FABRIC_CLK => DATA_ADC3[52]) = (100:100:100, 100:100:100);
    (FABRIC_CLK => DATA_ADC3[53]) = (100:100:100, 100:100:100);
    (FABRIC_CLK => DATA_ADC3[54]) = (100:100:100, 100:100:100);
    (FABRIC_CLK => DATA_ADC3[55]) = (100:100:100, 100:100:100);
    (FABRIC_CLK => DATA_ADC3[56]) = (100:100:100, 100:100:100);
    (FABRIC_CLK => DATA_ADC3[57]) = (100:100:100, 100:100:100);
    (FABRIC_CLK => DATA_ADC3[58]) = (100:100:100, 100:100:100);
    (FABRIC_CLK => DATA_ADC3[59]) = (100:100:100, 100:100:100);
    (FABRIC_CLK => DATA_ADC3[5]) = (100:100:100, 100:100:100);
    (FABRIC_CLK => DATA_ADC3[60]) = (100:100:100, 100:100:100);
    (FABRIC_CLK => DATA_ADC3[61]) = (100:100:100, 100:100:100);
    (FABRIC_CLK => DATA_ADC3[62]) = (100:100:100, 100:100:100);
    (FABRIC_CLK => DATA_ADC3[63]) = (100:100:100, 100:100:100);
    (FABRIC_CLK => DATA_ADC3[64]) = (100:100:100, 100:100:100);
    (FABRIC_CLK => DATA_ADC3[65]) = (100:100:100, 100:100:100);
    (FABRIC_CLK => DATA_ADC3[66]) = (100:100:100, 100:100:100);
    (FABRIC_CLK => DATA_ADC3[67]) = (100:100:100, 100:100:100);
    (FABRIC_CLK => DATA_ADC3[68]) = (100:100:100, 100:100:100);
    (FABRIC_CLK => DATA_ADC3[69]) = (100:100:100, 100:100:100);
    (FABRIC_CLK => DATA_ADC3[6]) = (100:100:100, 100:100:100);
    (FABRIC_CLK => DATA_ADC3[70]) = (100:100:100, 100:100:100);
    (FABRIC_CLK => DATA_ADC3[71]) = (100:100:100, 100:100:100);
    (FABRIC_CLK => DATA_ADC3[72]) = (100:100:100, 100:100:100);
    (FABRIC_CLK => DATA_ADC3[73]) = (100:100:100, 100:100:100);
    (FABRIC_CLK => DATA_ADC3[74]) = (100:100:100, 100:100:100);
    (FABRIC_CLK => DATA_ADC3[75]) = (100:100:100, 100:100:100);
    (FABRIC_CLK => DATA_ADC3[76]) = (100:100:100, 100:100:100);
    (FABRIC_CLK => DATA_ADC3[77]) = (100:100:100, 100:100:100);
    (FABRIC_CLK => DATA_ADC3[78]) = (100:100:100, 100:100:100);
    (FABRIC_CLK => DATA_ADC3[79]) = (100:100:100, 100:100:100);
    (FABRIC_CLK => DATA_ADC3[7]) = (100:100:100, 100:100:100);
    (FABRIC_CLK => DATA_ADC3[80]) = (100:100:100, 100:100:100);
    (FABRIC_CLK => DATA_ADC3[81]) = (100:100:100, 100:100:100);
    (FABRIC_CLK => DATA_ADC3[82]) = (100:100:100, 100:100:100);
    (FABRIC_CLK => DATA_ADC3[83]) = (100:100:100, 100:100:100);
    (FABRIC_CLK => DATA_ADC3[84]) = (100:100:100, 100:100:100);
    (FABRIC_CLK => DATA_ADC3[85]) = (100:100:100, 100:100:100);
    (FABRIC_CLK => DATA_ADC3[86]) = (100:100:100, 100:100:100);
    (FABRIC_CLK => DATA_ADC3[87]) = (100:100:100, 100:100:100);
    (FABRIC_CLK => DATA_ADC3[88]) = (100:100:100, 100:100:100);
    (FABRIC_CLK => DATA_ADC3[89]) = (100:100:100, 100:100:100);
    (FABRIC_CLK => DATA_ADC3[8]) = (100:100:100, 100:100:100);
    (FABRIC_CLK => DATA_ADC3[90]) = (100:100:100, 100:100:100);
    (FABRIC_CLK => DATA_ADC3[91]) = (100:100:100, 100:100:100);
    (FABRIC_CLK => DATA_ADC3[92]) = (100:100:100, 100:100:100);
    (FABRIC_CLK => DATA_ADC3[93]) = (100:100:100, 100:100:100);
    (FABRIC_CLK => DATA_ADC3[94]) = (100:100:100, 100:100:100);
    (FABRIC_CLK => DATA_ADC3[95]) = (100:100:100, 100:100:100);
    (FABRIC_CLK => DATA_ADC3[96]) = (100:100:100, 100:100:100);
    (FABRIC_CLK => DATA_ADC3[97]) = (100:100:100, 100:100:100);
    (FABRIC_CLK => DATA_ADC3[98]) = (100:100:100, 100:100:100);
    (FABRIC_CLK => DATA_ADC3[99]) = (100:100:100, 100:100:100);
    (FABRIC_CLK => DATA_ADC3[9]) = (100:100:100, 100:100:100);
    (FABRIC_CLK => STATUS_ADC0[10]) = (100:100:100, 100:100:100);
    (FABRIC_CLK => STATUS_ADC0[11]) = (100:100:100, 100:100:100);
    (FABRIC_CLK => STATUS_ADC0[12]) = (100:100:100, 100:100:100);
    (FABRIC_CLK => STATUS_ADC0[8]) = (100:100:100, 100:100:100);
    (FABRIC_CLK => STATUS_ADC0[9]) = (100:100:100, 100:100:100);
    (FABRIC_CLK => STATUS_ADC1[10]) = (100:100:100, 100:100:100);
    (FABRIC_CLK => STATUS_ADC1[11]) = (100:100:100, 100:100:100);
    (FABRIC_CLK => STATUS_ADC1[12]) = (100:100:100, 100:100:100);
    (FABRIC_CLK => STATUS_ADC1[8]) = (100:100:100, 100:100:100);
    (FABRIC_CLK => STATUS_ADC1[9]) = (100:100:100, 100:100:100);
    (FABRIC_CLK => STATUS_ADC2[10]) = (100:100:100, 100:100:100);
    (FABRIC_CLK => STATUS_ADC2[11]) = (100:100:100, 100:100:100);
    (FABRIC_CLK => STATUS_ADC2[12]) = (100:100:100, 100:100:100);
    (FABRIC_CLK => STATUS_ADC2[8]) = (100:100:100, 100:100:100);
    (FABRIC_CLK => STATUS_ADC2[9]) = (100:100:100, 100:100:100);
    (FABRIC_CLK => STATUS_ADC3[10]) = (100:100:100, 100:100:100);
    (FABRIC_CLK => STATUS_ADC3[11]) = (100:100:100, 100:100:100);
    (FABRIC_CLK => STATUS_ADC3[12]) = (100:100:100, 100:100:100);
    (FABRIC_CLK => STATUS_ADC3[8]) = (100:100:100, 100:100:100);
    (FABRIC_CLK => STATUS_ADC3[9]) = (100:100:100, 100:100:100);
    (FABRIC_CLK => STATUS_COMMON[5]) = (100:100:100, 100:100:100);
`ifdef XIL_TIMING
    $period (negedge CLK_ADC, 0:0:0, notifier);
    $period (negedge CLK_FIFO_LM, 0:0:0, notifier);
    $period (negedge DCLK, 0:0:0, notifier);
    $period (negedge FABRIC_CLK, 0:0:0, notifier);
    $period (negedge PLL_DMON_OUT, 0:0:0, notifier);
    $period (negedge PLL_MONCLK, 0:0:0, notifier);
    $period (negedge PLL_REFCLK_IN, 0:0:0, notifier);
    $period (negedge PLL_REFCLK_OUT, 0:0:0, notifier);
    $period (posedge CLK_ADC, 0:0:0, notifier);
    $period (posedge CLK_FIFO_LM, 0:0:0, notifier);
    $period (posedge DCLK, 0:0:0, notifier);
    $period (posedge FABRIC_CLK, 0:0:0, notifier);
    $period (posedge PLL_DMON_OUT, 0:0:0, notifier);
    $period (posedge PLL_MONCLK, 0:0:0, notifier);
    $period (posedge PLL_REFCLK_IN, 0:0:0, notifier);
    $period (posedge PLL_REFCLK_OUT, 0:0:0, notifier);
    $setuphold (posedge DCLK, negedge CONTROL_ADC0[13], 0:0:0, 0:0:0, notifier, , , DCLK_delay, CONTROL_ADC0_delay[13]);
    $setuphold (posedge DCLK, negedge CONTROL_ADC0[14], 0:0:0, 0:0:0, notifier, , , DCLK_delay, CONTROL_ADC0_delay[14]);
    $setuphold (posedge DCLK, negedge CONTROL_ADC0[15], 0:0:0, 0:0:0, notifier, , , DCLK_delay, CONTROL_ADC0_delay[15]);
    $setuphold (posedge DCLK, negedge CONTROL_ADC0[2], 0:0:0, 0:0:0, notifier, , , DCLK_delay, CONTROL_ADC0_delay[2]);
    $setuphold (posedge DCLK, negedge CONTROL_ADC0[3], 0:0:0, 0:0:0, notifier, , , DCLK_delay, CONTROL_ADC0_delay[3]);
    $setuphold (posedge DCLK, negedge CONTROL_ADC0[4], 0:0:0, 0:0:0, notifier, , , DCLK_delay, CONTROL_ADC0_delay[4]);
    $setuphold (posedge DCLK, negedge CONTROL_ADC0[5], 0:0:0, 0:0:0, notifier, , , DCLK_delay, CONTROL_ADC0_delay[5]);
    $setuphold (posedge DCLK, negedge CONTROL_ADC0[6], 0:0:0, 0:0:0, notifier, , , DCLK_delay, CONTROL_ADC0_delay[6]);
    $setuphold (posedge DCLK, negedge CONTROL_ADC1[13], 0:0:0, 0:0:0, notifier, , , DCLK_delay, CONTROL_ADC1_delay[13]);
    $setuphold (posedge DCLK, negedge CONTROL_ADC1[14], 0:0:0, 0:0:0, notifier, , , DCLK_delay, CONTROL_ADC1_delay[14]);
    $setuphold (posedge DCLK, negedge CONTROL_ADC1[15], 0:0:0, 0:0:0, notifier, , , DCLK_delay, CONTROL_ADC1_delay[15]);
    $setuphold (posedge DCLK, negedge CONTROL_ADC1[2], 0:0:0, 0:0:0, notifier, , , DCLK_delay, CONTROL_ADC1_delay[2]);
    $setuphold (posedge DCLK, negedge CONTROL_ADC1[3], 0:0:0, 0:0:0, notifier, , , DCLK_delay, CONTROL_ADC1_delay[3]);
    $setuphold (posedge DCLK, negedge CONTROL_ADC1[4], 0:0:0, 0:0:0, notifier, , , DCLK_delay, CONTROL_ADC1_delay[4]);
    $setuphold (posedge DCLK, negedge CONTROL_ADC1[5], 0:0:0, 0:0:0, notifier, , , DCLK_delay, CONTROL_ADC1_delay[5]);
    $setuphold (posedge DCLK, negedge CONTROL_ADC1[6], 0:0:0, 0:0:0, notifier, , , DCLK_delay, CONTROL_ADC1_delay[6]);
    $setuphold (posedge DCLK, negedge CONTROL_ADC2[13], 0:0:0, 0:0:0, notifier, , , DCLK_delay, CONTROL_ADC2_delay[13]);
    $setuphold (posedge DCLK, negedge CONTROL_ADC2[14], 0:0:0, 0:0:0, notifier, , , DCLK_delay, CONTROL_ADC2_delay[14]);
    $setuphold (posedge DCLK, negedge CONTROL_ADC2[15], 0:0:0, 0:0:0, notifier, , , DCLK_delay, CONTROL_ADC2_delay[15]);
    $setuphold (posedge DCLK, negedge CONTROL_ADC2[2], 0:0:0, 0:0:0, notifier, , , DCLK_delay, CONTROL_ADC2_delay[2]);
    $setuphold (posedge DCLK, negedge CONTROL_ADC2[3], 0:0:0, 0:0:0, notifier, , , DCLK_delay, CONTROL_ADC2_delay[3]);
    $setuphold (posedge DCLK, negedge CONTROL_ADC2[4], 0:0:0, 0:0:0, notifier, , , DCLK_delay, CONTROL_ADC2_delay[4]);
    $setuphold (posedge DCLK, negedge CONTROL_ADC2[5], 0:0:0, 0:0:0, notifier, , , DCLK_delay, CONTROL_ADC2_delay[5]);
    $setuphold (posedge DCLK, negedge CONTROL_ADC2[6], 0:0:0, 0:0:0, notifier, , , DCLK_delay, CONTROL_ADC2_delay[6]);
    $setuphold (posedge DCLK, negedge CONTROL_ADC3[13], 0:0:0, 0:0:0, notifier, , , DCLK_delay, CONTROL_ADC3_delay[13]);
    $setuphold (posedge DCLK, negedge CONTROL_ADC3[14], 0:0:0, 0:0:0, notifier, , , DCLK_delay, CONTROL_ADC3_delay[14]);
    $setuphold (posedge DCLK, negedge CONTROL_ADC3[15], 0:0:0, 0:0:0, notifier, , , DCLK_delay, CONTROL_ADC3_delay[15]);
    $setuphold (posedge DCLK, negedge CONTROL_ADC3[2], 0:0:0, 0:0:0, notifier, , , DCLK_delay, CONTROL_ADC3_delay[2]);
    $setuphold (posedge DCLK, negedge CONTROL_ADC3[3], 0:0:0, 0:0:0, notifier, , , DCLK_delay, CONTROL_ADC3_delay[3]);
    $setuphold (posedge DCLK, negedge CONTROL_ADC3[4], 0:0:0, 0:0:0, notifier, , , DCLK_delay, CONTROL_ADC3_delay[4]);
    $setuphold (posedge DCLK, negedge CONTROL_ADC3[5], 0:0:0, 0:0:0, notifier, , , DCLK_delay, CONTROL_ADC3_delay[5]);
    $setuphold (posedge DCLK, negedge CONTROL_ADC3[6], 0:0:0, 0:0:0, notifier, , , DCLK_delay, CONTROL_ADC3_delay[6]);
    $setuphold (posedge DCLK, negedge CONTROL_COMMON[3], 0:0:0, 0:0:0, notifier, , , DCLK_delay, CONTROL_COMMON_delay[3]);
    $setuphold (posedge DCLK, negedge DADDR[0], 0:0:0, 0:0:0, notifier, , , DCLK_delay, DADDR_delay[0]);
    $setuphold (posedge DCLK, negedge DADDR[10], 0:0:0, 0:0:0, notifier, , , DCLK_delay, DADDR_delay[10]);
    $setuphold (posedge DCLK, negedge DADDR[1], 0:0:0, 0:0:0, notifier, , , DCLK_delay, DADDR_delay[1]);
    $setuphold (posedge DCLK, negedge DADDR[2], 0:0:0, 0:0:0, notifier, , , DCLK_delay, DADDR_delay[2]);
    $setuphold (posedge DCLK, negedge DADDR[3], 0:0:0, 0:0:0, notifier, , , DCLK_delay, DADDR_delay[3]);
    $setuphold (posedge DCLK, negedge DADDR[4], 0:0:0, 0:0:0, notifier, , , DCLK_delay, DADDR_delay[4]);
    $setuphold (posedge DCLK, negedge DADDR[5], 0:0:0, 0:0:0, notifier, , , DCLK_delay, DADDR_delay[5]);
    $setuphold (posedge DCLK, negedge DADDR[6], 0:0:0, 0:0:0, notifier, , , DCLK_delay, DADDR_delay[6]);
    $setuphold (posedge DCLK, negedge DADDR[7], 0:0:0, 0:0:0, notifier, , , DCLK_delay, DADDR_delay[7]);
    $setuphold (posedge DCLK, negedge DADDR[8], 0:0:0, 0:0:0, notifier, , , DCLK_delay, DADDR_delay[8]);
    $setuphold (posedge DCLK, negedge DADDR[9], 0:0:0, 0:0:0, notifier, , , DCLK_delay, DADDR_delay[9]);
    $setuphold (posedge DCLK, negedge DEN, 0:0:0, 0:0:0, notifier, , , DCLK_delay, DEN_delay);
    $setuphold (posedge DCLK, negedge DI[0], 0:0:0, 0:0:0, notifier, , , DCLK_delay, DI_delay[0]);
    $setuphold (posedge DCLK, negedge DI[10], 0:0:0, 0:0:0, notifier, , , DCLK_delay, DI_delay[10]);
    $setuphold (posedge DCLK, negedge DI[11], 0:0:0, 0:0:0, notifier, , , DCLK_delay, DI_delay[11]);
    $setuphold (posedge DCLK, negedge DI[12], 0:0:0, 0:0:0, notifier, , , DCLK_delay, DI_delay[12]);
    $setuphold (posedge DCLK, negedge DI[13], 0:0:0, 0:0:0, notifier, , , DCLK_delay, DI_delay[13]);
    $setuphold (posedge DCLK, negedge DI[14], 0:0:0, 0:0:0, notifier, , , DCLK_delay, DI_delay[14]);
    $setuphold (posedge DCLK, negedge DI[15], 0:0:0, 0:0:0, notifier, , , DCLK_delay, DI_delay[15]);
    $setuphold (posedge DCLK, negedge DI[1], 0:0:0, 0:0:0, notifier, , , DCLK_delay, DI_delay[1]);
    $setuphold (posedge DCLK, negedge DI[2], 0:0:0, 0:0:0, notifier, , , DCLK_delay, DI_delay[2]);
    $setuphold (posedge DCLK, negedge DI[3], 0:0:0, 0:0:0, notifier, , , DCLK_delay, DI_delay[3]);
    $setuphold (posedge DCLK, negedge DI[4], 0:0:0, 0:0:0, notifier, , , DCLK_delay, DI_delay[4]);
    $setuphold (posedge DCLK, negedge DI[5], 0:0:0, 0:0:0, notifier, , , DCLK_delay, DI_delay[5]);
    $setuphold (posedge DCLK, negedge DI[6], 0:0:0, 0:0:0, notifier, , , DCLK_delay, DI_delay[6]);
    $setuphold (posedge DCLK, negedge DI[7], 0:0:0, 0:0:0, notifier, , , DCLK_delay, DI_delay[7]);
    $setuphold (posedge DCLK, negedge DI[8], 0:0:0, 0:0:0, notifier, , , DCLK_delay, DI_delay[8]);
    $setuphold (posedge DCLK, negedge DI[9], 0:0:0, 0:0:0, notifier, , , DCLK_delay, DI_delay[9]);
    $setuphold (posedge DCLK, negedge DWE, 0:0:0, 0:0:0, notifier, , , DCLK_delay, DWE_delay);
    $setuphold (posedge DCLK, posedge CONTROL_ADC0[13], 0:0:0, 0:0:0, notifier, , , DCLK_delay, CONTROL_ADC0_delay[13]);
    $setuphold (posedge DCLK, posedge CONTROL_ADC0[14], 0:0:0, 0:0:0, notifier, , , DCLK_delay, CONTROL_ADC0_delay[14]);
    $setuphold (posedge DCLK, posedge CONTROL_ADC0[15], 0:0:0, 0:0:0, notifier, , , DCLK_delay, CONTROL_ADC0_delay[15]);
    $setuphold (posedge DCLK, posedge CONTROL_ADC0[2], 0:0:0, 0:0:0, notifier, , , DCLK_delay, CONTROL_ADC0_delay[2]);
    $setuphold (posedge DCLK, posedge CONTROL_ADC0[3], 0:0:0, 0:0:0, notifier, , , DCLK_delay, CONTROL_ADC0_delay[3]);
    $setuphold (posedge DCLK, posedge CONTROL_ADC0[4], 0:0:0, 0:0:0, notifier, , , DCLK_delay, CONTROL_ADC0_delay[4]);
    $setuphold (posedge DCLK, posedge CONTROL_ADC0[5], 0:0:0, 0:0:0, notifier, , , DCLK_delay, CONTROL_ADC0_delay[5]);
    $setuphold (posedge DCLK, posedge CONTROL_ADC0[6], 0:0:0, 0:0:0, notifier, , , DCLK_delay, CONTROL_ADC0_delay[6]);
    $setuphold (posedge DCLK, posedge CONTROL_ADC1[13], 0:0:0, 0:0:0, notifier, , , DCLK_delay, CONTROL_ADC1_delay[13]);
    $setuphold (posedge DCLK, posedge CONTROL_ADC1[14], 0:0:0, 0:0:0, notifier, , , DCLK_delay, CONTROL_ADC1_delay[14]);
    $setuphold (posedge DCLK, posedge CONTROL_ADC1[15], 0:0:0, 0:0:0, notifier, , , DCLK_delay, CONTROL_ADC1_delay[15]);
    $setuphold (posedge DCLK, posedge CONTROL_ADC1[2], 0:0:0, 0:0:0, notifier, , , DCLK_delay, CONTROL_ADC1_delay[2]);
    $setuphold (posedge DCLK, posedge CONTROL_ADC1[3], 0:0:0, 0:0:0, notifier, , , DCLK_delay, CONTROL_ADC1_delay[3]);
    $setuphold (posedge DCLK, posedge CONTROL_ADC1[4], 0:0:0, 0:0:0, notifier, , , DCLK_delay, CONTROL_ADC1_delay[4]);
    $setuphold (posedge DCLK, posedge CONTROL_ADC1[5], 0:0:0, 0:0:0, notifier, , , DCLK_delay, CONTROL_ADC1_delay[5]);
    $setuphold (posedge DCLK, posedge CONTROL_ADC1[6], 0:0:0, 0:0:0, notifier, , , DCLK_delay, CONTROL_ADC1_delay[6]);
    $setuphold (posedge DCLK, posedge CONTROL_ADC2[13], 0:0:0, 0:0:0, notifier, , , DCLK_delay, CONTROL_ADC2_delay[13]);
    $setuphold (posedge DCLK, posedge CONTROL_ADC2[14], 0:0:0, 0:0:0, notifier, , , DCLK_delay, CONTROL_ADC2_delay[14]);
    $setuphold (posedge DCLK, posedge CONTROL_ADC2[15], 0:0:0, 0:0:0, notifier, , , DCLK_delay, CONTROL_ADC2_delay[15]);
    $setuphold (posedge DCLK, posedge CONTROL_ADC2[2], 0:0:0, 0:0:0, notifier, , , DCLK_delay, CONTROL_ADC2_delay[2]);
    $setuphold (posedge DCLK, posedge CONTROL_ADC2[3], 0:0:0, 0:0:0, notifier, , , DCLK_delay, CONTROL_ADC2_delay[3]);
    $setuphold (posedge DCLK, posedge CONTROL_ADC2[4], 0:0:0, 0:0:0, notifier, , , DCLK_delay, CONTROL_ADC2_delay[4]);
    $setuphold (posedge DCLK, posedge CONTROL_ADC2[5], 0:0:0, 0:0:0, notifier, , , DCLK_delay, CONTROL_ADC2_delay[5]);
    $setuphold (posedge DCLK, posedge CONTROL_ADC2[6], 0:0:0, 0:0:0, notifier, , , DCLK_delay, CONTROL_ADC2_delay[6]);
    $setuphold (posedge DCLK, posedge CONTROL_ADC3[13], 0:0:0, 0:0:0, notifier, , , DCLK_delay, CONTROL_ADC3_delay[13]);
    $setuphold (posedge DCLK, posedge CONTROL_ADC3[14], 0:0:0, 0:0:0, notifier, , , DCLK_delay, CONTROL_ADC3_delay[14]);
    $setuphold (posedge DCLK, posedge CONTROL_ADC3[15], 0:0:0, 0:0:0, notifier, , , DCLK_delay, CONTROL_ADC3_delay[15]);
    $setuphold (posedge DCLK, posedge CONTROL_ADC3[2], 0:0:0, 0:0:0, notifier, , , DCLK_delay, CONTROL_ADC3_delay[2]);
    $setuphold (posedge DCLK, posedge CONTROL_ADC3[3], 0:0:0, 0:0:0, notifier, , , DCLK_delay, CONTROL_ADC3_delay[3]);
    $setuphold (posedge DCLK, posedge CONTROL_ADC3[4], 0:0:0, 0:0:0, notifier, , , DCLK_delay, CONTROL_ADC3_delay[4]);
    $setuphold (posedge DCLK, posedge CONTROL_ADC3[5], 0:0:0, 0:0:0, notifier, , , DCLK_delay, CONTROL_ADC3_delay[5]);
    $setuphold (posedge DCLK, posedge CONTROL_ADC3[6], 0:0:0, 0:0:0, notifier, , , DCLK_delay, CONTROL_ADC3_delay[6]);
    $setuphold (posedge DCLK, posedge CONTROL_COMMON[3], 0:0:0, 0:0:0, notifier, , , DCLK_delay, CONTROL_COMMON_delay[3]);
    $setuphold (posedge DCLK, posedge DADDR[0], 0:0:0, 0:0:0, notifier, , , DCLK_delay, DADDR_delay[0]);
    $setuphold (posedge DCLK, posedge DADDR[10], 0:0:0, 0:0:0, notifier, , , DCLK_delay, DADDR_delay[10]);
    $setuphold (posedge DCLK, posedge DADDR[1], 0:0:0, 0:0:0, notifier, , , DCLK_delay, DADDR_delay[1]);
    $setuphold (posedge DCLK, posedge DADDR[2], 0:0:0, 0:0:0, notifier, , , DCLK_delay, DADDR_delay[2]);
    $setuphold (posedge DCLK, posedge DADDR[3], 0:0:0, 0:0:0, notifier, , , DCLK_delay, DADDR_delay[3]);
    $setuphold (posedge DCLK, posedge DADDR[4], 0:0:0, 0:0:0, notifier, , , DCLK_delay, DADDR_delay[4]);
    $setuphold (posedge DCLK, posedge DADDR[5], 0:0:0, 0:0:0, notifier, , , DCLK_delay, DADDR_delay[5]);
    $setuphold (posedge DCLK, posedge DADDR[6], 0:0:0, 0:0:0, notifier, , , DCLK_delay, DADDR_delay[6]);
    $setuphold (posedge DCLK, posedge DADDR[7], 0:0:0, 0:0:0, notifier, , , DCLK_delay, DADDR_delay[7]);
    $setuphold (posedge DCLK, posedge DADDR[8], 0:0:0, 0:0:0, notifier, , , DCLK_delay, DADDR_delay[8]);
    $setuphold (posedge DCLK, posedge DADDR[9], 0:0:0, 0:0:0, notifier, , , DCLK_delay, DADDR_delay[9]);
    $setuphold (posedge DCLK, posedge DEN, 0:0:0, 0:0:0, notifier, , , DCLK_delay, DEN_delay);
    $setuphold (posedge DCLK, posedge DI[0], 0:0:0, 0:0:0, notifier, , , DCLK_delay, DI_delay[0]);
    $setuphold (posedge DCLK, posedge DI[10], 0:0:0, 0:0:0, notifier, , , DCLK_delay, DI_delay[10]);
    $setuphold (posedge DCLK, posedge DI[11], 0:0:0, 0:0:0, notifier, , , DCLK_delay, DI_delay[11]);
    $setuphold (posedge DCLK, posedge DI[12], 0:0:0, 0:0:0, notifier, , , DCLK_delay, DI_delay[12]);
    $setuphold (posedge DCLK, posedge DI[13], 0:0:0, 0:0:0, notifier, , , DCLK_delay, DI_delay[13]);
    $setuphold (posedge DCLK, posedge DI[14], 0:0:0, 0:0:0, notifier, , , DCLK_delay, DI_delay[14]);
    $setuphold (posedge DCLK, posedge DI[15], 0:0:0, 0:0:0, notifier, , , DCLK_delay, DI_delay[15]);
    $setuphold (posedge DCLK, posedge DI[1], 0:0:0, 0:0:0, notifier, , , DCLK_delay, DI_delay[1]);
    $setuphold (posedge DCLK, posedge DI[2], 0:0:0, 0:0:0, notifier, , , DCLK_delay, DI_delay[2]);
    $setuphold (posedge DCLK, posedge DI[3], 0:0:0, 0:0:0, notifier, , , DCLK_delay, DI_delay[3]);
    $setuphold (posedge DCLK, posedge DI[4], 0:0:0, 0:0:0, notifier, , , DCLK_delay, DI_delay[4]);
    $setuphold (posedge DCLK, posedge DI[5], 0:0:0, 0:0:0, notifier, , , DCLK_delay, DI_delay[5]);
    $setuphold (posedge DCLK, posedge DI[6], 0:0:0, 0:0:0, notifier, , , DCLK_delay, DI_delay[6]);
    $setuphold (posedge DCLK, posedge DI[7], 0:0:0, 0:0:0, notifier, , , DCLK_delay, DI_delay[7]);
    $setuphold (posedge DCLK, posedge DI[8], 0:0:0, 0:0:0, notifier, , , DCLK_delay, DI_delay[8]);
    $setuphold (posedge DCLK, posedge DI[9], 0:0:0, 0:0:0, notifier, , , DCLK_delay, DI_delay[9]);
    $setuphold (posedge DCLK, posedge DWE, 0:0:0, 0:0:0, notifier, , , DCLK_delay, DWE_delay);
    $setuphold (posedge FABRIC_CLK, negedge CONTROL_COMMON[12], 0:0:0, 0:0:0, notifier, , , FABRIC_CLK_delay, CONTROL_COMMON_delay[12]);
    $setuphold (posedge FABRIC_CLK, posedge CONTROL_COMMON[12], 0:0:0, 0:0:0, notifier, , , FABRIC_CLK_delay, CONTROL_COMMON_delay[12]);
    $width (negedge CLK_FIFO_LM, 0:0:0, 0, notifier);
    $width (negedge DCLK, 0:0:0, 0, notifier);
    $width (negedge FABRIC_CLK, 0:0:0, 0, notifier);
    $width (negedge PLL_MONCLK, 0:0:0, 0, notifier);
    $width (negedge PLL_REFCLK_IN, 0:0:0, 0, notifier);
    $width (posedge CLK_FIFO_LM, 0:0:0, 0, notifier);
    $width (posedge DCLK, 0:0:0, 0, notifier);
    $width (posedge FABRIC_CLK, 0:0:0, 0, notifier);
    $width (posedge PLL_MONCLK, 0:0:0, 0, notifier);
    $width (posedge PLL_REFCLK_IN, 0:0:0, 0, notifier);
`endif
    specparam PATHPULSE$ = 0;
  endspecify
`endif
endmodule

`endcelldefine
