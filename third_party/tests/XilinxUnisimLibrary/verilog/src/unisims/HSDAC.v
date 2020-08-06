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
//  /   /                        HSDAC
// /___/   /\      Filename    : HSDAC.v
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

module HSDAC #(
`ifdef XIL_TIMING
  parameter LOC = "UNPLACED",
`endif
  parameter SIM_DEVICE = "ULTRASCALE_PLUS",
  parameter integer XPA_CFG0 = 0,
  parameter integer XPA_CFG1 = 0,
  parameter integer XPA_NUM_DACS = 0,
  parameter integer XPA_NUM_DUCS = 0,
  parameter XPA_PLL_USED = "No",
  parameter integer XPA_SAMPLE_RATE_MSPS = 0
)(
  output CLK_DAC,
  output [15:0] DOUT,
  output DRDY,
  output PLL_DMON_OUT,
  output PLL_REFCLK_OUT,
  output [15:0] STATUS_COMMON,
  output [15:0] STATUS_DAC0,
  output [15:0] STATUS_DAC1,
  output [15:0] STATUS_DAC2,
  output [15:0] STATUS_DAC3,
  output SYSREF_OUT_NORTH,
  output SYSREF_OUT_SOUTH,
  output VOUT0_N,
  output VOUT0_P,
  output VOUT1_N,
  output VOUT1_P,
  output VOUT2_N,
  output VOUT2_P,
  output VOUT3_N,
  output VOUT3_P,

  input CLK_FIFO_LM,
  input [15:0] CONTROL_COMMON,
  input [15:0] CONTROL_DAC0,
  input [15:0] CONTROL_DAC1,
  input [15:0] CONTROL_DAC2,
  input [15:0] CONTROL_DAC3,
  input DAC_CLK_N,
  input DAC_CLK_P,
  input [11:0] DADDR,
  input [255:0] DATA_DAC0,
  input [255:0] DATA_DAC1,
  input [255:0] DATA_DAC2,
  input [255:0] DATA_DAC3,
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
  input SYSREF_P
);

// define constants
  localparam MODULE_NAME = "HSDAC";
  
  reg trig_attr = 1'b0;
// include dynamic registers - XILINX test only
`ifdef XIL_DR
  `include "HSDAC_dr.v"
`else
  localparam [152:1] SIM_DEVICE_REG = SIM_DEVICE;
  localparam [15:0] XPA_CFG0_REG = XPA_CFG0;
  localparam [15:0] XPA_CFG1_REG = XPA_CFG1;
  localparam [2:0] XPA_NUM_DACS_REG = XPA_NUM_DACS;
  localparam [2:0] XPA_NUM_DUCS_REG = XPA_NUM_DUCS;
  localparam [24:1] XPA_PLL_USED_REG = XPA_PLL_USED;
  localparam [13:0] XPA_SAMPLE_RATE_MSPS_REG = XPA_SAMPLE_RATE_MSPS;
`endif

`ifdef XIL_ATTR_TEST
  reg attr_test = 1'b1;
`else
  reg attr_test = 1'b0;
`endif

  reg attr_err = 1'b0;
  tri0 glblGSR = glbl.GSR;

  wire CLK_DAC_SPARE_out;
  wire CLK_DAC_out;
  wire DRDY_out;
  wire PLL_DMON_OUT_out;
  wire PLL_REFCLK_OUT_out;
  wire SYSREF_OUT_NORTH_out;
  wire SYSREF_OUT_SOUTH_out;
  wire VOUT0_N_out;
  wire VOUT0_P_out;
  wire VOUT1_N_out;
  wire VOUT1_P_out;
  wire VOUT2_N_out;
  wire VOUT2_P_out;
  wire VOUT3_N_out;
  wire VOUT3_P_out;
  wire [15:0] DOUT_out;
  wire [15:0] STATUS_COMMON_out;
  wire [15:0] STATUS_DAC0_out;
  wire [15:0] STATUS_DAC1_out;
  wire [15:0] STATUS_DAC2_out;
  wire [15:0] STATUS_DAC3_out;
  wire [15:0] TEST_STATUS_out;
  wire [1:0] PLL_SCAN_OUT_B_FD_out;
  wire [299:0] TEST_SO_out;

  wire CLK_FIFO_LM_in;
  wire DAC_CLK_N_in;
  wire DAC_CLK_P_in;
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
  wire TEST_SCAN_MODE_B_in;
  wire TEST_SCAN_RESET_in;
  wire TEST_SE_B_in;
  wire [11:0] DADDR_in;
  wire [15:0] CONTROL_COMMON_in;
  wire [15:0] CONTROL_DAC0_in;
  wire [15:0] CONTROL_DAC1_in;
  wire [15:0] CONTROL_DAC2_in;
  wire [15:0] CONTROL_DAC3_in;
  wire [15:0] DI_in;
  wire [15:0] TEST_SCAN_CTRL_in;
  wire [1:0] PLL_SCAN_CLK_FD_in;
  wire [1:0] PLL_SCAN_IN_FD_in;
  wire [255:0] DATA_DAC0_in;
  wire [255:0] DATA_DAC1_in;
  wire [255:0] DATA_DAC2_in;
  wire [255:0] DATA_DAC3_in;
  wire [299:0] TEST_SI_in;
  wire [4:0] TEST_SCAN_CLK_in;

`ifdef XIL_TIMING
  wire DCLK_delay;
  wire DEN_delay;
  wire DWE_delay;
  wire FABRIC_CLK_delay;
  wire [11:0] DADDR_delay;
  wire [15:0] CONTROL_COMMON_delay;
  wire [15:0] DI_delay;
`endif

  real VOUT0_N_real;
  real VOUT0_P_real;
  real VOUT1_N_real;
  real VOUT1_P_real;
  real VOUT2_N_real;
  real VOUT2_P_real;
  real VOUT3_N_real;
  real VOUT3_P_real;

  assign CLK_DAC = CLK_DAC_out;
  assign DOUT = DOUT_out;
  assign DRDY = DRDY_out;
  assign PLL_DMON_OUT = PLL_DMON_OUT_out;
  assign PLL_REFCLK_OUT = PLL_REFCLK_OUT_out;
  assign STATUS_COMMON = STATUS_COMMON_out;
  assign STATUS_DAC0 = STATUS_DAC0_out;
  assign STATUS_DAC1 = STATUS_DAC1_out;
  assign STATUS_DAC2 = STATUS_DAC2_out;
  assign STATUS_DAC3 = STATUS_DAC3_out;
  assign SYSREF_OUT_NORTH = SYSREF_OUT_NORTH_out;
  assign SYSREF_OUT_SOUTH = SYSREF_OUT_SOUTH_out;
  assign VOUT0_N = VOUT0_N_out;
  assign VOUT0_P = VOUT0_P_out;
  assign VOUT1_N = VOUT1_N_out;
  assign VOUT1_P = VOUT1_P_out;
  assign VOUT2_N = VOUT2_N_out;
  assign VOUT2_P = VOUT2_P_out;
  assign VOUT3_N = VOUT3_N_out;
  assign VOUT3_P = VOUT3_P_out;

`ifdef XIL_TIMING
  assign CONTROL_COMMON_in = CONTROL_COMMON_delay;
  assign DADDR_in = DADDR_delay;
  assign DCLK_in = DCLK_delay;
  assign DEN_in = DEN_delay;
  assign DI_in = DI_delay;
  assign DWE_in = DWE_delay;
  assign FABRIC_CLK_in = FABRIC_CLK_delay;
`else
  assign CONTROL_COMMON_in = CONTROL_COMMON;
  assign DADDR_in = DADDR;
  assign DCLK_in = DCLK;
  assign DEN_in = DEN;
  assign DI_in = DI;
  assign DWE_in = DWE;
  assign FABRIC_CLK_in = FABRIC_CLK;
`endif

  assign CLK_FIFO_LM_in = CLK_FIFO_LM;
  assign CONTROL_DAC0_in = CONTROL_DAC0;
  assign CONTROL_DAC1_in = CONTROL_DAC1;
  assign CONTROL_DAC2_in = CONTROL_DAC2;
  assign CONTROL_DAC3_in = CONTROL_DAC3;
  assign DAC_CLK_N_in = DAC_CLK_N;
  assign DAC_CLK_P_in = DAC_CLK_P;
  assign DATA_DAC0_in = DATA_DAC0;
  assign DATA_DAC1_in = DATA_DAC1;
  assign DATA_DAC2_in = DATA_DAC2;
  assign DATA_DAC3_in = DATA_DAC3;
  assign PLL_MONCLK_in = PLL_MONCLK;
  assign PLL_REFCLK_IN_in = PLL_REFCLK_IN;
  assign SYSREF_IN_NORTH_in = SYSREF_IN_NORTH;
  assign SYSREF_IN_SOUTH_in = SYSREF_IN_SOUTH;
  assign SYSREF_N_in = SYSREF_N;
  assign SYSREF_P_in = SYSREF_P;

`ifndef XIL_XECLIB
always @ (trig_attr) begin
  #1;
  if ((attr_test == 1'b1) ||
      ((SIM_DEVICE_REG != "ULTRASCALE_PLUS") &&
       (SIM_DEVICE_REG != "ULTRASCALE_PLUS_ES1") &&
       (SIM_DEVICE_REG != "ULTRASCALE_PLUS_ES2"))) begin
    $display("Error: [Unisim %s-101] SIM_DEVICE attribute is set to %s.  Legal values for this attribute are ULTRASCALE_PLUS, ULTRASCALE_PLUS_ES1 or ULTRASCALE_PLUS_ES2. Instance: %m", MODULE_NAME, SIM_DEVICE_REG);
    attr_err = 1'b1;
  end
  
  if ((attr_test == 1'b1) ||
      ((XPA_CFG0_REG < 0) || (XPA_CFG0_REG > 65535))) begin
    $display("Error: [Unisim %s-102] XPA_CFG0 attribute is set to %d.  Legal values for this attribute are 0 to 65535. Instance: %m", MODULE_NAME, XPA_CFG0_REG);
    attr_err = 1'b1;
  end
  
  if ((attr_test == 1'b1) ||
      ((XPA_CFG1_REG < 0) || (XPA_CFG1_REG > 65535))) begin
    $display("Error: [Unisim %s-103] XPA_CFG1 attribute is set to %d.  Legal values for this attribute are 0 to 65535. Instance: %m", MODULE_NAME, XPA_CFG1_REG);
    attr_err = 1'b1;
  end
  
  if ((attr_test == 1'b1) ||
      ((XPA_NUM_DACS_REG < 0) || (XPA_NUM_DACS_REG > 4))) begin
    $display("Error: [Unisim %s-104] XPA_NUM_DACS attribute is set to %d.  Legal values for this attribute are 0 to 4. Instance: %m", MODULE_NAME, XPA_NUM_DACS_REG);
    attr_err = 1'b1;
  end
  
  if ((attr_test == 1'b1) ||
      ((XPA_NUM_DUCS_REG < 0) || (XPA_NUM_DUCS_REG > 4))) begin
    $display("Error: [Unisim %s-105] XPA_NUM_DUCS attribute is set to %d.  Legal values for this attribute are 0 to 4. Instance: %m", MODULE_NAME, XPA_NUM_DUCS_REG);
    attr_err = 1'b1;
  end
  
  if ((attr_test == 1'b1) ||
      ((XPA_PLL_USED_REG != "No") &&
       (XPA_PLL_USED_REG != "Yes"))) begin
    $display("Error: [Unisim %s-106] XPA_PLL_USED attribute is set to %s.  Legal values for this attribute are No or Yes. Instance: %m", MODULE_NAME, XPA_PLL_USED_REG);
    attr_err = 1'b1;
  end
  
  if ((attr_test == 1'b1) ||
      ((XPA_SAMPLE_RATE_MSPS_REG < 0) || (XPA_SAMPLE_RATE_MSPS_REG > 10000))) begin
    $display("Error: [Unisim %s-107] XPA_SAMPLE_RATE_MSPS attribute is set to %d.  Legal values for this attribute are 0 to 10000. Instance: %m", MODULE_NAME, XPA_SAMPLE_RATE_MSPS_REG);
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

SIP_HSDAC SIP_HSDAC_INST (
  .SIM_DEVICE (SIM_DEVICE_REG),
  .CLK_DAC (CLK_DAC_out),
  .CLK_DAC_SPARE (CLK_DAC_SPARE_out),
  .DOUT (DOUT_out),
  .DRDY (DRDY_out),
  .PLL_DMON_OUT (PLL_DMON_OUT_out),
  .PLL_REFCLK_OUT (PLL_REFCLK_OUT_out),
  .PLL_SCAN_OUT_B_FD (PLL_SCAN_OUT_B_FD_out),
  .STATUS_COMMON (STATUS_COMMON_out),
  .STATUS_DAC0 (STATUS_DAC0_out),
  .STATUS_DAC1 (STATUS_DAC1_out),
  .STATUS_DAC2 (STATUS_DAC2_out),
  .STATUS_DAC3 (STATUS_DAC3_out),
  .SYSREF_OUT_NORTH (SYSREF_OUT_NORTH_out),
  .SYSREF_OUT_SOUTH (SYSREF_OUT_SOUTH_out),
  .TEST_SO (TEST_SO_out),
  .TEST_STATUS (TEST_STATUS_out),
  .VOUT0_N (VOUT0_N_real),
  .VOUT0_P (VOUT0_P_real),
  .VOUT1_N (VOUT1_N_real),
  .VOUT1_P (VOUT1_P_real),
  .VOUT2_N (VOUT2_N_real),
  .VOUT2_P (VOUT2_P_real),
  .VOUT3_N (VOUT3_N_real),
  .VOUT3_P (VOUT3_P_real),
  .CLK_FIFO_LM (CLK_FIFO_LM_in),
  .CONTROL_COMMON (CONTROL_COMMON_in),
  .CONTROL_DAC0 (CONTROL_DAC0_in),
  .CONTROL_DAC1 (CONTROL_DAC1_in),
  .CONTROL_DAC2 (CONTROL_DAC2_in),
  .CONTROL_DAC3 (CONTROL_DAC3_in),
  .DAC_CLK_N (DAC_CLK_N_in),
  .DAC_CLK_P (DAC_CLK_P_in),
  .DADDR (DADDR_in),
  .DATA_DAC0 (DATA_DAC0_in),
  .DATA_DAC1 (DATA_DAC1_in),
  .DATA_DAC2 (DATA_DAC2_in),
  .DATA_DAC3 (DATA_DAC3_in),
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
  .TEST_SCAN_CLK (TEST_SCAN_CLK_in),
  .TEST_SCAN_CTRL (TEST_SCAN_CTRL_in),
  .TEST_SCAN_MODE_B (TEST_SCAN_MODE_B_in),
  .TEST_SCAN_RESET (TEST_SCAN_RESET_in),
  .TEST_SE_B (TEST_SE_B_in),
  .TEST_SI (TEST_SI_in),
  .GSR (glblGSR)
);

`ifndef XIL_XECLIB
`ifdef XIL_TIMING
  reg notifier;
`endif

  specify
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
`ifdef XIL_TIMING
    $period (negedge CLK_DAC, 0:0:0, notifier);
    $period (negedge CLK_FIFO_LM, 0:0:0, notifier);
    $period (negedge DCLK, 0:0:0, notifier);
    $period (negedge FABRIC_CLK, 0:0:0, notifier);
    $period (negedge PLL_DMON_OUT, 0:0:0, notifier);
    $period (negedge PLL_MONCLK, 0:0:0, notifier);
    $period (negedge PLL_REFCLK_IN, 0:0:0, notifier);
    $period (negedge PLL_REFCLK_OUT, 0:0:0, notifier);
    $period (posedge CLK_DAC, 0:0:0, notifier);
    $period (posedge CLK_FIFO_LM, 0:0:0, notifier);
    $period (posedge DCLK, 0:0:0, notifier);
    $period (posedge FABRIC_CLK, 0:0:0, notifier);
    $period (posedge PLL_DMON_OUT, 0:0:0, notifier);
    $period (posedge PLL_MONCLK, 0:0:0, notifier);
    $period (posedge PLL_REFCLK_IN, 0:0:0, notifier);
    $period (posedge PLL_REFCLK_OUT, 0:0:0, notifier);
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
    $setuphold (posedge FABRIC_CLK, negedge CONTROL_COMMON[15], 0:0:0, 0:0:0, notifier, , , FABRIC_CLK_delay, CONTROL_COMMON_delay[15]);
    $setuphold (posedge FABRIC_CLK, posedge CONTROL_COMMON[15], 0:0:0, 0:0:0, notifier, , , FABRIC_CLK_delay, CONTROL_COMMON_delay[15]);
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
