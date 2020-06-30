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
// /___/  \  /    Vendor      : Xilinx
// \   \   \/     Version     : 2016.3
//  \   \         Description : Xilinx Unified Simulation Library Component
//  /   /                       Xilinx Analog-to-Digital Converter and System Monitor
// /___/   /\     Filename    : SYSMONE4.v
// \   \  /  \    
//  \___\/\___\
//
///////////////////////////////////////////////////////////////////////////////
// Revision:
//
//  End Revision:
///////////////////////////////////////////////////////////////////////////////

`timescale 1ps / 1ps

`celldefine

  module SYSMONE4 #(
`ifdef XIL_TIMING
  parameter LOC = "UNPLACED",
`endif
  parameter [15:0] COMMON_N_SOURCE = 16'hFFFF,
  parameter [15:0] INIT_40 = 16'h0000,
  parameter [15:0] INIT_41 = 16'h0000,
  parameter [15:0] INIT_42 = 16'h0000,
  parameter [15:0] INIT_43 = 16'h0000,
  parameter [15:0] INIT_44 = 16'h0000,
  parameter [15:0] INIT_45 = 16'h0000,
  parameter [15:0] INIT_46 = 16'h0000,
  parameter [15:0] INIT_47 = 16'h0000,
  parameter [15:0] INIT_48 = 16'h0000,
  parameter [15:0] INIT_49 = 16'h0000,
  parameter [15:0] INIT_4A = 16'h0000,
  parameter [15:0] INIT_4B = 16'h0000,
  parameter [15:0] INIT_4C = 16'h0000,
  parameter [15:0] INIT_4D = 16'h0000,
  parameter [15:0] INIT_4E = 16'h0000,
  parameter [15:0] INIT_4F = 16'h0000,
  parameter [15:0] INIT_50 = 16'h0000,
  parameter [15:0] INIT_51 = 16'h0000,
  parameter [15:0] INIT_52 = 16'h0000,
  parameter [15:0] INIT_53 = 16'h0000,
  parameter [15:0] INIT_54 = 16'h0000,
  parameter [15:0] INIT_55 = 16'h0000,
  parameter [15:0] INIT_56 = 16'h0000,
  parameter [15:0] INIT_57 = 16'h0000,
  parameter [15:0] INIT_58 = 16'h0000,
  parameter [15:0] INIT_59 = 16'h0000,
  parameter [15:0] INIT_5A = 16'h0000,
  parameter [15:0] INIT_5B = 16'h0000,
  parameter [15:0] INIT_5C = 16'h0000,
  parameter [15:0] INIT_5D = 16'h0000,
  parameter [15:0] INIT_5E = 16'h0000,
  parameter [15:0] INIT_5F = 16'h0000,
  parameter [15:0] INIT_60 = 16'h0000,
  parameter [15:0] INIT_61 = 16'h0000,
  parameter [15:0] INIT_62 = 16'h0000,
  parameter [15:0] INIT_63 = 16'h0000,
  parameter [15:0] INIT_64 = 16'h0000,
  parameter [15:0] INIT_65 = 16'h0000,
  parameter [15:0] INIT_66 = 16'h0000,
  parameter [15:0] INIT_67 = 16'h0000,
  parameter [15:0] INIT_68 = 16'h0000,
  parameter [15:0] INIT_69 = 16'h0000,
  parameter [15:0] INIT_6A = 16'h0000,
  parameter [15:0] INIT_6B = 16'h0000,
  parameter [15:0] INIT_6C = 16'h0000,
  parameter [15:0] INIT_6D = 16'h0000,
  parameter [15:0] INIT_6E = 16'h0000,
  parameter [15:0] INIT_6F = 16'h0000,
  parameter [15:0] INIT_70 = 16'h0000,
  parameter [15:0] INIT_71 = 16'h0000,
  parameter [15:0] INIT_72 = 16'h0000,
  parameter [15:0] INIT_73 = 16'h0000,
  parameter [15:0] INIT_74 = 16'h0000,
  parameter [15:0] INIT_75 = 16'h0000,
  parameter [15:0] INIT_76 = 16'h0000,
  parameter [15:0] INIT_77 = 16'h0000,
  parameter [15:0] INIT_78 = 16'h0000,
  parameter [15:0] INIT_79 = 16'h0000,
  parameter [15:0] INIT_7A = 16'h0000,
  parameter [15:0] INIT_7B = 16'h0000,
  parameter [15:0] INIT_7C = 16'h0000,
  parameter [15:0] INIT_7D = 16'h0000,
  parameter [15:0] INIT_7E = 16'h0000,
  parameter [15:0] INIT_7F = 16'h0000,
  parameter [0:0] IS_CONVSTCLK_INVERTED = 1'b0,
  parameter [0:0] IS_DCLK_INVERTED = 1'b0,
  parameter SIM_DEVICE = "ULTRASCALE_PLUS",   
  parameter SIM_MONITOR_FILE = "design.txt",
  parameter integer SYSMON_VUSER0_BANK = 0,
  parameter SYSMON_VUSER0_MONITOR = "NONE",
  parameter integer SYSMON_VUSER1_BANK = 0,
  parameter SYSMON_VUSER1_MONITOR = "NONE",
  parameter integer SYSMON_VUSER2_BANK = 0,
  parameter SYSMON_VUSER2_MONITOR = "NONE",
  parameter integer SYSMON_VUSER3_BANK = 0,
  parameter SYSMON_VUSER3_MONITOR = "NONE"        
)(
  output [15:0] ADC_DATA,
  output [15:0] ALM,
  output BUSY,
  output [5:0] CHANNEL,
  output [15:0] DO,
  output DRDY,
  output EOC,
  output EOS,
  output I2C_SCLK_TS,
  output I2C_SDA_TS,
  output JTAGBUSY,
  output JTAGLOCKED,
  output JTAGMODIFIED,
  output [4:0] MUXADDR,
  output OT,
  output SMBALERT_TS,
  
  input CONVST,
  input CONVSTCLK,
  input [7:0] DADDR,
  input DCLK,
  input DEN,
  input [15:0] DI,
  input DWE,
  input I2C_SCLK,
  input I2C_SDA,
  input RESET,
  input [15:0] VAUXN,
  input [15:0] VAUXP,
  input VN,
  input VP
  );

// define constants
  localparam MODULE_NAME = "SYSMONE4";

// Parameter encodings and registers
  //localparam SIM_DEVICE_ULTRASCALE_PLUS = 0;
  //localparam SIM_DEVICE_ULTRASCALE_PLUS_ES1 = 1;
  //localparam SIM_DEVICE_ZYNQ_ULTRASCALE = 2;
  //localparam SIM_DEVICE_ZYNQ_ULTRASCALE_ES1 = 3;
  //localparam SIM_MONITOR_FILE_design_txt = 0;
  //localparam SYSMON_VUSER0_MONITOR_NONE = 0;
  //localparam SYSMON_VUSER1_MONITOR_NONE = 0;
  //localparam SYSMON_VUSER2_MONITOR_NONE = 0;
  //localparam SYSMON_VUSER3_MONITOR_NONE = 0;

  reg trig_attr = 1'b0;
  reg trig_dep_attr = 1'b0;
  reg trig_i2c_addr = 1'b0;
// include dynamic registers - XILINX test only
`ifdef XIL_DR
  `include "SYSMONE4_dr.v"
`else
  localparam [15:0] COMMON_N_SOURCE_REG = COMMON_N_SOURCE;
  localparam [15:0] INIT_40_REG = INIT_40;
  localparam [15:0] INIT_41_REG = INIT_41;
  localparam [15:0] INIT_42_REG = INIT_42;
  localparam [15:0] INIT_43_REG = INIT_43;
  localparam [15:0] INIT_44_REG = INIT_44;
  localparam [15:0] INIT_45_REG = INIT_45;
  localparam [15:0] INIT_46_REG = INIT_46;
  localparam [15:0] INIT_47_REG = INIT_47;
  localparam [15:0] INIT_48_REG = INIT_48;
  localparam [15:0] INIT_49_REG = INIT_49;
  localparam [15:0] INIT_4A_REG = INIT_4A;
  localparam [15:0] INIT_4B_REG = INIT_4B;
  localparam [15:0] INIT_4C_REG = INIT_4C;
  localparam [15:0] INIT_4D_REG = INIT_4D;
  localparam [15:0] INIT_4E_REG = INIT_4E;
  localparam [15:0] INIT_4F_REG = INIT_4F;
  localparam [15:0] INIT_50_REG = INIT_50;
  localparam [15:0] INIT_51_REG = INIT_51;
  localparam [15:0] INIT_52_REG = INIT_52;
  localparam [15:0] INIT_53_REG = INIT_53;
  localparam [15:0] INIT_54_REG = INIT_54;
  localparam [15:0] INIT_55_REG = INIT_55;
  localparam [15:0] INIT_56_REG = INIT_56;
  localparam [15:0] INIT_57_REG = INIT_57;
  localparam [15:0] INIT_58_REG = INIT_58;
  localparam [15:0] INIT_59_REG = INIT_59;
  localparam [15:0] INIT_5A_REG = INIT_5A;
  localparam [15:0] INIT_5B_REG = INIT_5B;
  localparam [15:0] INIT_5C_REG = INIT_5C;
  localparam [15:0] INIT_5D_REG = INIT_5D;
  localparam [15:0] INIT_5E_REG = INIT_5E;
  localparam [15:0] INIT_5F_REG = INIT_5F;
  localparam [15:0] INIT_60_REG = INIT_60;
  localparam [15:0] INIT_61_REG = INIT_61;
  localparam [15:0] INIT_62_REG = INIT_62;
  localparam [15:0] INIT_63_REG = INIT_63;
  localparam [15:0] INIT_64_REG = INIT_64;
  localparam [15:0] INIT_65_REG = INIT_65;
  localparam [15:0] INIT_66_REG = INIT_66;
  localparam [15:0] INIT_67_REG = INIT_67;
  localparam [15:0] INIT_68_REG = INIT_68;
  localparam [15:0] INIT_69_REG = INIT_69;
  localparam [15:0] INIT_6A_REG = INIT_6A;
  localparam [15:0] INIT_6B_REG = INIT_6B;
  localparam [15:0] INIT_6C_REG = INIT_6C;
  localparam [15:0] INIT_6D_REG = INIT_6D;
  localparam [15:0] INIT_6E_REG = INIT_6E;
  localparam [15:0] INIT_6F_REG = INIT_6F;
  localparam [15:0] INIT_70_REG = INIT_70;
  localparam [15:0] INIT_71_REG = INIT_71;
  localparam [15:0] INIT_72_REG = INIT_72;
  localparam [15:0] INIT_73_REG = INIT_73;
  localparam [15:0] INIT_74_REG = INIT_74;
  localparam [15:0] INIT_75_REG = INIT_75;
  localparam [15:0] INIT_76_REG = INIT_76;
  localparam [15:0] INIT_77_REG = INIT_77;
  localparam [15:0] INIT_78_REG = INIT_78;
  localparam [15:0] INIT_79_REG = INIT_79;
  localparam [15:0] INIT_7A_REG = INIT_7A;
  localparam [15:0] INIT_7B_REG = INIT_7B;
  localparam [15:0] INIT_7C_REG = INIT_7C;
  localparam [15:0] INIT_7D_REG = INIT_7D;
  localparam [15:0] INIT_7E_REG = INIT_7E;
  localparam [15:0] INIT_7F_REG = INIT_7F;
  localparam [0:0] IS_CONVSTCLK_INVERTED_REG = IS_CONVSTCLK_INVERTED;
  localparam [0:0] IS_DCLK_INVERTED_REG = IS_DCLK_INVERTED;
  localparam [152:1] SIM_DEVICE_REG = SIM_DEVICE;
  localparam [80:1] SIM_MONITOR_FILE_REG = SIM_MONITOR_FILE;
  localparam  [9:0] SYSMON_VUSER0_BANK_REG = SYSMON_VUSER0_BANK;
  localparam [32:1] SYSMON_VUSER0_MONITOR_REG = SYSMON_VUSER0_MONITOR;
  localparam  [9:0] SYSMON_VUSER1_BANK_REG = SYSMON_VUSER1_BANK;
  localparam [32:1] SYSMON_VUSER1_MONITOR_REG = SYSMON_VUSER1_MONITOR;
  localparam  [9:0] SYSMON_VUSER2_BANK_REG = SYSMON_VUSER2_BANK;
  localparam [32:1] SYSMON_VUSER2_MONITOR_REG = SYSMON_VUSER2_MONITOR;
  localparam  [9:0] SYSMON_VUSER3_BANK_REG = SYSMON_VUSER3_BANK;
  localparam [32:1] SYSMON_VUSER3_MONITOR_REG = SYSMON_VUSER3_MONITOR;
`endif

  wire [15:0] COMMON_N_SOURCE_BIN;
  wire [15:0] INIT_40_BIN;
  wire [15:0] INIT_41_BIN;
  wire [15:0] INIT_42_BIN;
  wire [15:0] INIT_43_BIN;
  wire [15:0] INIT_44_BIN;
  wire [15:0] INIT_45_BIN;
  wire [15:0] INIT_46_BIN;
  wire [15:0] INIT_47_BIN;
  wire [15:0] INIT_48_BIN;
  wire [15:0] INIT_49_BIN;
  wire [15:0] INIT_4A_BIN;
  wire [15:0] INIT_4B_BIN;
  wire [15:0] INIT_4C_BIN;
  wire [15:0] INIT_4D_BIN;
  wire [15:0] INIT_4E_BIN;
  wire [15:0] INIT_4F_BIN;
  wire [15:0] INIT_50_BIN;
  wire [15:0] INIT_51_BIN;
  wire [15:0] INIT_52_BIN;
  wire [15:0] INIT_53_BIN;
  wire [15:0] INIT_54_BIN;
  wire [15:0] INIT_55_BIN;
  wire [15:0] INIT_56_BIN;
  wire [15:0] INIT_57_BIN;
  wire [15:0] INIT_58_BIN;
  wire [15:0] INIT_59_BIN;
  wire [15:0] INIT_5A_BIN;
  wire [15:0] INIT_5B_BIN;
  wire [15:0] INIT_5C_BIN;
  wire [15:0] INIT_5D_BIN;
  wire [15:0] INIT_5E_BIN;
  wire [15:0] INIT_5F_BIN;
  wire [15:0] INIT_60_BIN;
  wire [15:0] INIT_61_BIN;
  wire [15:0] INIT_62_BIN;
  wire [15:0] INIT_63_BIN;
  wire [15:0] INIT_64_BIN;
  wire [15:0] INIT_65_BIN;
  wire [15:0] INIT_66_BIN;
  wire [15:0] INIT_67_BIN;
  wire [15:0] INIT_68_BIN;
  wire [15:0] INIT_69_BIN;
  wire [15:0] INIT_6A_BIN;
  wire [15:0] INIT_6B_BIN;
  wire [15:0] INIT_6C_BIN;
  wire [15:0] INIT_6D_BIN;
  wire [15:0] INIT_6E_BIN;
  wire [15:0] INIT_6F_BIN;
  wire [15:0] INIT_70_BIN;
  wire [15:0] INIT_71_BIN;
  wire [15:0] INIT_72_BIN;
  wire [15:0] INIT_73_BIN;
  wire [15:0] INIT_74_BIN;
  wire [15:0] INIT_75_BIN;
  wire [15:0] INIT_76_BIN;
  wire [15:0] INIT_77_BIN;
  wire [15:0] INIT_78_BIN;
  wire [15:0] INIT_79_BIN;
  wire [15:0] INIT_7A_BIN;
  wire [15:0] INIT_7B_BIN;
  wire [15:0] INIT_7C_BIN;
  wire [15:0] INIT_7D_BIN;
  wire [15:0] INIT_7E_BIN;
  wire [15:0] INIT_7F_BIN;
  wire IS_CONVSTCLK_INVERTED_BIN;
  wire IS_DCLK_INVERTED_BIN;
  wire [1:0] SIM_DEVICE_BIN;
  wire SIM_MONITOR_FILE_BIN;
  wire [9:0] SYSMON_VUSER0_BANK_BIN;
  wire SYSMON_VUSER0_MONITOR_BIN;
  wire [9:0] SYSMON_VUSER1_BANK_BIN;
  wire SYSMON_VUSER1_MONITOR_BIN;
  wire [9:0] SYSMON_VUSER2_BANK_BIN;
  wire SYSMON_VUSER2_MONITOR_BIN;
  wire [9:0] SYSMON_VUSER3_BANK_BIN;
  wire SYSMON_VUSER3_MONITOR_BIN;

  `ifdef XIL_ATTR_TEST
    reg attr_test = 1'b1;
  `else
    reg attr_test = 1'b0;
  `endif
  reg attr_err = 1'b0;
   tri0 glblGSR = glbl.GSR;

  reg BUSY_out;
  reg DRDY_out;
  reg EOC_out;
  reg EOS_out;
  wire I2C_SCLK_TS_out;
  reg  I2C_SDA_TS_out;
  wire JTAGBUSY_out;
  wire JTAGLOCKED_out;
  wire JTAGMODIFIED_out;
  reg OT_out;
  reg  SMBALERT_TS_out;
  reg  [15:0] ADC_DATA_out;
  reg [15:0] ALM_out;
  reg [15:0] DO_out;
  reg [4:0] MUXADDR_out;
  reg [5:0] CHANNEL_out;

  wire CONVSTCLK_in;
  wire CONVST_in;
  wire DCLK_in;
  wire DEN_in;
  wire DWE_in;
  wire I2C_SCLK_in;
  wire I2C_SDA_in;
  wire RESET_in;
  wire VN_in;
  wire VP_in;
  wire [15:0] DI_in;
  wire [15:0] VAUXN_in;
  wire [15:0] VAUXP_in;
  wire [7:0] DADDR_in;


`ifdef XIL_TIMING
  wire DCLK_delay;
  wire DEN_delay;
  wire DWE_delay;
  wire [15:0] DI_delay;
  wire [7:0] DADDR_delay;
`endif

  assign ADC_DATA = ADC_DATA_out;
  assign ALM = ALM_out;
  assign BUSY = BUSY_out;
  assign CHANNEL = CHANNEL_out;
  assign DO = DO_out;
  assign DRDY = DRDY_out;
  assign EOC = EOC_out;
  assign EOS = EOS_out;
  assign I2C_SCLK_TS = I2C_SCLK_TS_out;
  assign I2C_SDA_TS  = I2C_SDA_TS_out;
  assign JTAGBUSY = JTAGBUSY_out;
  assign JTAGLOCKED = JTAGLOCKED_out;
  assign JTAGMODIFIED = JTAGMODIFIED_out;
  assign MUXADDR = MUXADDR_out;
  assign OT = OT_out;
  assign SMBALERT_TS = SMBALERT_TS_out;

  wire [7:0] DADDR_inv;
  wire DCLK_inv;
  wire DEN_inv;
  wire DWE_inv;
  wire RESET_in_inv;
  wire [15:0] DI_inv;
  wire I2C_SCLK_inv;
  wire I2C_SDA_inv;

  `ifdef XIL_TIMING
    assign DADDR_inv = DADDR_delay;
    assign DCLK_inv = DCLK_delay;
    assign DEN_inv = DEN_delay;
    assign DI_inv = DI_delay; 
    assign DWE_inv = DWE_delay;
  `else
    assign DADDR_inv = DADDR;
    assign DCLK_inv = DCLK;
    assign DEN_inv = DEN;
    assign DI_inv = DI; 
    assign DWE_inv = DWE;
  `endif
  assign I2C_SCLK_inv = I2C_SCLK;
  assign I2C_SDA_inv  = I2C_SDA;

  assign DADDR_in = DADDR_inv ^ 7'b0000000;
  assign DCLK_in = DCLK_inv ^ IS_DCLK_INVERTED_BIN;
  assign DEN_in = DEN_inv ^ 1'b0;
  assign DI_in = DI_inv ^ 16'h0000;
  assign DWE_in = DWE_inv ^ 1'b0;
  assign RESET_in      = RESET;
  assign CONVSTCLK_in   = CONVSTCLK ^ IS_CONVSTCLK_INVERTED_BIN;
  assign CONVST_in  = CONVST ^ 1'b0;
  assign I2C_SCLK_in = I2C_SCLK_inv ^ 1'b0;
  assign I2C_SDA_in = I2C_SDA_inv ^ 1'b0;
  assign VAUXN_in = VAUXN;
  assign VAUXP_in = VAUXP;
  assign VN_in = VN;
  assign VP_in = VP;

  assign COMMON_N_SOURCE_BIN = COMMON_N_SOURCE_REG;
  
  assign INIT_40_BIN = INIT_40_REG;
  
  assign INIT_41_BIN = INIT_41_REG;
  
  assign INIT_42_BIN = INIT_42_REG;
  
  assign INIT_43_BIN = INIT_43_REG;
  
  assign INIT_44_BIN = INIT_44_REG;
  
  assign INIT_45_BIN = INIT_45_REG;
  
  assign INIT_46_BIN = INIT_46_REG;
  
  assign INIT_47_BIN = INIT_47_REG;
  
  assign INIT_48_BIN = INIT_48_REG;
  
  assign INIT_49_BIN = INIT_49_REG;
  
  assign INIT_4A_BIN = INIT_4A_REG;
  
  assign INIT_4B_BIN = INIT_4B_REG;
  
  assign INIT_4C_BIN = INIT_4C_REG;
  
  assign INIT_4D_BIN = INIT_4D_REG;
  
  assign INIT_4E_BIN = INIT_4E_REG;
  
  assign INIT_4F_BIN = INIT_4F_REG;
  
  assign INIT_50_BIN = INIT_50_REG;
  
  assign INIT_51_BIN = INIT_51_REG;
  
  assign INIT_52_BIN = INIT_52_REG;
  
  assign INIT_53_BIN = INIT_53_REG;
  
  assign INIT_54_BIN = INIT_54_REG;
  
  assign INIT_55_BIN = INIT_55_REG;
  
  assign INIT_56_BIN = INIT_56_REG;
  
  assign INIT_57_BIN = INIT_57_REG;
  
  assign INIT_58_BIN = INIT_58_REG;
  
  assign INIT_59_BIN = INIT_59_REG;
  
  assign INIT_5A_BIN = INIT_5A_REG;
  
  assign INIT_5B_BIN = INIT_5B_REG;
  
  assign INIT_5C_BIN = INIT_5C_REG;
  
  assign INIT_5D_BIN = INIT_5D_REG;
  
  assign INIT_5E_BIN = INIT_5E_REG;
  
  assign INIT_5F_BIN = INIT_5F_REG;
  
  assign INIT_60_BIN = INIT_60_REG;
  
  assign INIT_61_BIN = INIT_61_REG;
  
  assign INIT_62_BIN = INIT_62_REG;
  
  assign INIT_63_BIN = INIT_63_REG;
  
  assign INIT_64_BIN = INIT_64_REG;
  
  assign INIT_65_BIN = INIT_65_REG;
  
  assign INIT_66_BIN = INIT_66_REG;
  
  assign INIT_67_BIN = INIT_67_REG;
  
  assign INIT_68_BIN = INIT_68_REG;
  
  assign INIT_69_BIN = INIT_69_REG;
  
  assign INIT_6A_BIN = INIT_6A_REG;
  
  assign INIT_6B_BIN = INIT_6B_REG;
  
  assign INIT_6C_BIN = INIT_6C_REG;
  
  assign INIT_6D_BIN = INIT_6D_REG;
  
  assign INIT_6E_BIN = INIT_6E_REG;
  
  assign INIT_6F_BIN = INIT_6F_REG;
  
  assign INIT_70_BIN = INIT_70_REG;
  
  assign INIT_71_BIN = INIT_71_REG;
  
  assign INIT_72_BIN = INIT_72_REG;
  
  assign INIT_73_BIN = INIT_73_REG;
  
  assign INIT_74_BIN = INIT_74_REG;
  
  assign INIT_75_BIN = INIT_75_REG;
  
  assign INIT_76_BIN = INIT_76_REG;
  
  assign INIT_77_BIN = INIT_77_REG;
  
  assign INIT_78_BIN = INIT_78_REG;
  
  assign INIT_79_BIN = INIT_79_REG;
  
  assign INIT_7A_BIN = INIT_7A_REG;
  
  assign INIT_7B_BIN = INIT_7B_REG;
  
  assign INIT_7C_BIN = INIT_7C_REG;
  
  assign INIT_7D_BIN = INIT_7D_REG;
  
  assign INIT_7E_BIN = INIT_7E_REG;
  
  assign INIT_7F_BIN = INIT_7F_REG;
  
  assign IS_CONVSTCLK_INVERTED_BIN = IS_CONVSTCLK_INVERTED_REG;
  
  assign IS_DCLK_INVERTED_BIN = IS_DCLK_INVERTED_REG;

 // assign SIM_DEVICE_BIN =
 //     (SIM_DEVICE_REG == "ULTRASCALE_PLUS") ? SIM_DEVICE_ULTRASCALE_PLUS :
 //     (SIM_DEVICE_REG == "ULTRASCALE_PLUS_ES1") ? SIM_DEVICE_ULTRASCALE_PLUS_ES1 :
 //     (SIM_DEVICE_REG == "ZYNQ_ULTRASCALE") ? SIM_DEVICE_ZYNQ_ULTRASCALE :
 //     (SIM_DEVICE_REG == "ZYNQ_ULTRASCALE_ES1") ? SIM_DEVICE_ZYNQ_ULTRASCALE_ES1 :
 //      SIM_DEVICE_ULTRASCALE_PLUS;
 // 
 // assign SIM_MONITOR_FILE_BIN =
 //     (SIM_MONITOR_FILE_REG == "design.txt") ? SIM_MONITOR_FILE_design_txt :
 //      SIM_MONITOR_FILE_design_txt;
 // 
  assign SYSMON_VUSER0_BANK_BIN = SYSMON_VUSER0_BANK_REG;
  
 // assign SYSMON_VUSER0_MONITOR_BIN =
 //     (SYSMON_VUSER0_MONITOR_REG == "NONE") ? SYSMON_VUSER0_MONITOR_NONE :
 //      SYSMON_VUSER0_MONITOR_NONE;
  
  assign SYSMON_VUSER1_BANK_BIN = SYSMON_VUSER1_BANK_REG;
  
 // assign SYSMON_VUSER1_MONITOR_BIN =
 //     (SYSMON_VUSER1_MONITOR_REG == "NONE") ? SYSMON_VUSER1_MONITOR_NONE :
 //      SYSMON_VUSER1_MONITOR_NONE;
  
  assign SYSMON_VUSER2_BANK_BIN = SYSMON_VUSER2_BANK_REG;
  
 // assign SYSMON_VUSER2_MONITOR_BIN =
 //     (SYSMON_VUSER2_MONITOR_REG == "NONE") ? SYSMON_VUSER2_MONITOR_NONE :
 //      SYSMON_VUSER2_MONITOR_NONE;
  
  assign SYSMON_VUSER3_BANK_BIN = SYSMON_VUSER3_BANK_REG;
  
 // assign SYSMON_VUSER3_MONITOR_BIN =
 //     (SYSMON_VUSER3_MONITOR_REG == "NONE") ? SYSMON_VUSER3_MONITOR_NONE :
 //      SYSMON_VUSER3_MONITOR_NONE;

  initial begin
    trig_attr = 0;
    #1;
    trig_i2c_addr = 1;
    trig_attr = 1;
    #2 trig_dep_attr = 1;
  end

  time time_check;
  
  always @(posedge trig_attr) begin
    #1; 
    time_check=$time;
    if(time_check != 2)
      $display("Warning: [Unisim %s-69] SYSMONE4 time resolution has been overridden. It should be left as picoseconds. The model will not function correctly this way.", MODULE_NAME);

    if ((attr_test == 1'b1) ||
        ((SIM_DEVICE != "ULTRASCALE_PLUS") &&
         (SIM_DEVICE != "ULTRASCALE_PLUS_ES1") &&
         (SIM_DEVICE != "ULTRASCALE_PLUS_ES2") &&
         (SIM_DEVICE != "ZYNQ_ULTRASCALE") &&
         (SIM_DEVICE != "ZYNQ_ULTRASCALE_ES1") &&
         (SIM_DEVICE != "ZYNQ_ULTRASCALE_ES2") 
       )) begin
      $display("Error: [Unisim %s-168] SIM_DEVICE attribute is set to %s.  Legal values for this attribute are ULTRASCALE_PLUS, ULTRASCALE_PLUS_ES1, ULTRASCALE_PLUS_ES2, ZYNQ_ULTRASCALE, ZYNQ_ULTRASCALE_ES1, or ZYNQ_ULTRASCALE_ES2. Instance: %m", MODULE_NAME, SIM_DEVICE);
      attr_err = 1'b1;
    end
     
    if ((attr_test == 1'b1) ||
        ((SYSMON_VUSER0_BANK_REG < 0) || (SYSMON_VUSER0_BANK_REG > 999))) begin
      $display("Error: [Unisim %s-170] SYSMON_VUSER0_BANK attribute is set to %d.  Legal values for this attribute are 0 to 999. Instance: %m", MODULE_NAME, SYSMON_VUSER0_BANK_REG);
      attr_err = 1'b1;
    end
    
    if ((attr_test == 1'b1) ||
        ((SYSMON_VUSER1_BANK_REG < 0) || (SYSMON_VUSER1_BANK_REG > 999))) begin
      $display("Error: [Unisim %s-172] SYSMON_VUSER1_BANK attribute is set to %d.  Legal values for this attribute are 0 to 999. Instance: %m", MODULE_NAME, SYSMON_VUSER1_BANK_REG);
      attr_err = 1'b1;
    end
    
    if ((attr_test == 1'b1) ||
        ((SYSMON_VUSER2_BANK_REG < 0) || (SYSMON_VUSER2_BANK_REG > 999))) begin
      $display("Error: [Unisim %s-174] SYSMON_VUSER2_BANK attribute is set to %d.  Legal values for this attribute are 0 to 999. Instance: %m", MODULE_NAME, SYSMON_VUSER2_BANK_REG);
      attr_err = 1'b1;
    end
    
    if ((attr_test == 1'b1) ||
        ((SYSMON_VUSER3_BANK_REG < 0) || (SYSMON_VUSER3_BANK_REG > 999))) begin
      $display("Error: [Unisim %s-176] SYSMON_VUSER3_BANK attribute is set to %d.  Legal values for this attribute are 0 to 999. Instance: %m", MODULE_NAME, SYSMON_VUSER3_BANK_REG);
      attr_err = 1'b1;
    end
    
    if (attr_err == 1'b1) 
      #1 $finish;
       
  end // always @ (trig_attr)


  always @(trig_dep_attr)  begin

     if ((attr_test == 1'b1) ||
         ((INIT_41_BIN[15:12]==4'b0011) && (INIT_40_BIN[8]==1) && (INIT_40_BIN[5:0] != 6'b000011) && (INIT_40_BIN[5:0] < 6'b010000)))
           $display("Warning: [Unisim %s-1] INIT_40 attribute is set to %x.  Bit[8] of this attribute must be set to 0. Long acquistion mode is only allowed for external channels. Instance: %m", MODULE_NAME, INIT_40_BIN);

     if ((attr_test == 1'b1) ||
         ((INIT_41_BIN[15:12]!=4'b0011) && (INIT_4E_BIN[10:0]!=11'd0) && (INIT_4E_BIN[15:12]!=4'd0)))
           $display("Warning: [Unisim %s-2] INIT_4E attribute is set to %x.  Bit[15:12] and bit[10:0] of this attribute must be set to 0. Long acquistion mode is only allowed for external channels. Instance: %m", MODULE_NAME, INIT_4E_BIN);

     if ((attr_test == 1'b1) ||
         ((INIT_41_BIN[15:12]==4'b0011) && (INIT_40_BIN[13:12]!=2'b00) && (INIT_46_BIN != 16'h0000) && (INIT_48_BIN != 16'h0000) && (INIT_49_BIN != 16'h0000)))
           $display("Warning: [Unisim %s-3] INIT_46, INIT_48 and INIT_49 attributes are set to %x, %x, and %x respectively. These attributes must be set to 0000h in single channel mode with averaging enabled. Instance: %m", MODULE_NAME, INIT_46_BIN, INIT_48_BIN, INIT_49_BIN);

     if ((attr_test == 1'b1) || // CR 952216 
         (INIT_44_BIN[3:0]!=4'b0000))
           $display("Info: [Unisim %s-59] INIT_44[3:0] is set to %0b. For related VUSER banks, where 0-6V range has been selected, analog input file must reflect the selected input range. Instance: %m", MODULE_NAME, INIT_44_BIN[3:0]);

  end // always @ (trig_dep_attr)

   
  // Total UNISIM %s- warning message next: 70

  localparam CONV_CNT_P            = 37;
  localparam CONV_CNT              = 48; 

  //sequencer operation
  localparam [3:0] SEQ_DEFAULT_MODE   = 4'b0000 ;
  localparam [1:0] SEQ_DEFAULT_MODE2  = 2'b11   ;
  localparam [3:0] SEQ_SINGLE_PASS    = 4'b0001 ;
  localparam [3:0] SEQ_CONT_CHAN      = 4'b0010 ;
  localparam [3:0] SEQ_SINGLE_CHAN    = 4'b0011 ;//means sequencer is off

  //lr_rate
  localparam [1:0] LR_EVERY_OTHER     = 2'b00; 
  localparam [1:0] LR_EVERY_4TH       = 2'b01; 
  localparam [1:0] LR_EVERY_16TH      = 2'b10; 
  localparam [1:0] LR_EVERY_64TH      = 2'b11; 

  localparam [1:0] LR_EOS_HR_ONLY1    = 2'b00; 
  localparam [1:0] LR_EOS_LR_ONLY     = 2'b01; 
  localparam [1:0] LR_EOS_HR_LR       = 2'b10; 
  localparam [1:0] LR_EOS_HR_ONLY2    = 2'b11; 


  localparam OT_LIMIT_DEFAULT         = 16'hCB03;

  //adc_state
  localparam ST_A_FIRST_CALIB = 0,
             ST_A_CALIB       = 1,
             ST_A_WAIT        = 2,
             ST_A_CHAN        = 3,
             ST_A_ALM         = 4,
             ST_A_EOC         = 5,
             ST_A_WAIT_ED     = 6;

  localparam CMD_PAGE                   = 8'h00;
  localparam CMD_CLEAR_FAULT            = 8'h03;
  localparam CMD_CAPABILITY             = 8'h19;
  localparam CMD_VOUT_MODE              = 8'h20;
  localparam CMD_VOUT_OV_FAULT_LIMIT    = 8'h40;
  localparam CMD_VOUT_UV_FAULT_LIMIT    = 8'h44;
  localparam CMD_OT_FAULT_LIMIT         = 8'h4F;
  localparam CMD_OT_WARNING_LIMIT       = 8'h51;
  localparam CMD_UT_WARNING_LIMIT       = 8'h52;
  localparam CMD_UT_FAULT_LIMIT         = 8'h53;
  localparam CMD_STATUS_BYTE            = 8'h78;
  localparam CMD_STATUS_WORD            = 8'h79;
  localparam CMD_STATUS_VOUT            = 8'h7A;
  localparam CMD_STATUS_TEMPERATURE     = 8'h7D;
  localparam CMD_STATUS_CML             = 8'h7E;
  localparam CMD_READ_VOUT              = 8'h88;
  localparam CMD_READ_TEMPERATURE_1     = 8'h8D;
  localparam CMD_PMBUS_REVISION         = 8'h98;
  localparam CMD_MFR_ID                 = 8'h99;
  localparam CMD_MFR_MODEL              = 8'h9A;
  localparam CMD_MFR_REVISION           = 8'h9B;
  localparam CMD_MFR_SELECT_REG         = 8'hD0;
  localparam CMD_MFR_ACCESS_REG         = 8'hD1;
  localparam CMD_MFR_READ_VOUT_MAX      = 8'hD2;
  localparam CMD_MFR_READ_VOUT_MIN      = 8'hD3;
  localparam CMD_MFR_ENABLE_VUSER_HR    = 8'hD5;
  localparam CMD_MFR_READ_TEMP_MAX      = 8'hD6;
  localparam CMD_MFR_READ_TEMP_MIN      = 8'hD7;

  localparam eoc_distance               = 18;
  localparam alm_distance               = 15;

  time          time_out;
  time          prev_time_out;
  
  integer       temperature_index = -1;
  integer       time_index = -1;
  integer       vccaux_index = -1;
  integer       vccbram_index = -1;
  integer       vccint_index = -1;
  integer       vn_index = -1;
  integer       vp_index = -1;
  integer       vccpsintlp_index = -1;
  integer       vccpsintfp_index = -1;
  integer       vccpsaux_index = -1;
  integer       vauxp_idx[15:0]; 
  integer       vauxn_idx[15:0];
  integer       vuser0_index = -1;
  integer       vuser1_index = -1;
  integer       vuser2_index = -1;
  integer       vuser3_index = -1;
  integer       char_1;
  integer       char_2;
  integer       fs;
  integer       fd;
  integer       num_arg;
  integer       num_val;
  integer       adcclk_count;
  reg           adcclk_count_rst = 0;
  wire          adcclk_period_start;
  wire          adcclk_period_end;
  reg           adcclk_period_end_d;
  wire [8:0]    avg_amount;
  wire          avg_en;
  wire [1:0]    averaging;
  wire          avg_final_loop;
  wire          avg_final_loop_hr;
  wire          avg_final_loop_lr;
  wire          seq_lr_selected_p;
  reg           seq_lr_selected;
  reg [1:0]     seq_lr_selected_d;
  reg           add_channel_hr_p;
  reg           add_channel_lr_p;
  reg           add_channel;
  integer       conv_acc [63:0];
  integer       conv_result_int;
  integer       h, i, j, k, l, m, n, p;
  integer       file_line;

  // string    
  reg [8*12:1]  label0, label1, label2, label3, label4, label5, label6, label7, label8, label9, label10, label11, label12, label13, label14, label15, label16, label17, label18, label19, label20, label21, label22, label23, label24, label25, label26, label27, label28, label29, label30, label31, label32, label33, label34, label35, label36, label37, label38, label39, label40, label41, label42, label43, label44, label45, label46;
  reg [8*600:1] one_line;
  reg [8*12:1]  label [46:0];
  reg [8*12:1]  tmp_label;
  reg           end_of_file;
  
  real          tmp_va0; 
  real          tmp_va1;
  real          column_real00;
  real          column_real100;
  real          column_real101;
  real          column_real0, column_real1, column_real2, column_real3, column_real4, column_real5, column_real6, column_real7, column_real8, column_real9, column_real10, column_real11, column_real12, column_real13, column_real14, column_real15, column_real16, column_real17, column_real18, column_real19, column_real20, column_real21, column_real22, column_real23, column_real24, column_real25, column_real26, column_real27, column_real28, column_real29, column_real30, column_real31, column_real32, column_real33, column_real34, column_real35, column_real36, column_real37, column_real38, column_real39, column_real40, column_real41, column_real42, column_real43, column_real44, column_real45, column_real46;

  // array of real numbers
  reg [63:0]    column_real      [CONV_CNT-1  :0];
  reg [63:0]    chan_val         [CONV_CNT_P-1:0];
  reg [63:0]    chan_val_tmp     [CONV_CNT_P-1:0];
  reg [63:0]    chan_valn        [CONV_CNT_P-1:0];
  reg [63:0]    chan_valn_tmp    [CONV_CNT_P-1:0];
  reg [63:0]    mn_in_diff       [CONV_CNT_P-1:0];
  reg [63:0]    mn_in2_diff      [CONV_CNT_P-1:0];
  reg [63:0]    mn_in_uni        [CONV_CNT_P-1:0];
  reg [63:0]    mn_in2_uni       [CONV_CNT_P-1:0];
  reg [63:0]    mn_comm_in       [CONV_CNT_P-1:0];
  reg [63:0]    mn_comm2_in      [CONV_CNT_P-1:0];

  real          chan_val_p_tmp;
  real          chan_val_n_tmp;
  real          mn_mux_in;
  real          mn_in_tmp;
  real          mn_comm_in_tmp;
  real          mn_in_comm;
  real          tmp_v;
  real          tmp_v1;
  real          adc_temp_result;
  real          adc_intpwr_result;
  real          adc_ext_result;

  reg           init_rst;
  reg [2:0]     initialize;
  reg           int_rst_sync1;
  reg           int_rst_sync2;
  wire          int_rst_combined;
  wire          int_rst_combined_d;
  reg           alm_rst;
  reg           seq_rst;
  reg           soft_rst = 0;
  reg           en_data_flag;
  wire [15:0]   flag_reg0;
  wire [15:0]   flag_reg1;
  reg  [15:0]   ot_limit_reg = OT_LIMIT_DEFAULT;
  reg  [15:0]   tmp_otv;
  reg  [23:0]   conv_acc_vec;
  reg  [15:0]   conv_result;
  reg  [15:0]   conv_result_reg;
  reg  [15:0]   conv_acc_result;
  wire [7:0]    curr_clkdiv_sel;
  reg  [15:0]   alm_out_reg;
  reg  [15:0]   data_written;
  reg  [2:0]    adc_state;
  reg  [2:0]    adc_next_state;
  reg  [2:0]    adc_state_d_dclk;
  reg  [2:0]    adc_state_d;
  reg           st_first_calib_chan;

  reg           DRDY_out_pre1;
  reg           DRDY_out_pre2;
  reg           DRDY_out_pre3;
  reg           ot_out_reg;
  reg           ut_fault;  
  reg           ut_warn;  
  reg           ut_fault_reg; //under temperature fault register for PMBus capability.
  reg           ut_warn_reg; //under temperature warning register for PMBus capability.
  reg  [15:0]   alm_ut_reg; //under temperature fault registers for PMBUS capability
  reg  [11:1]   alm_ut;
  reg  [15:0]   DO_out_rdtmp;
  reg  [15:0]   data_reg [63:0];
  reg  [15:0]   dr_sram [255:64];
  reg           sysclk;
  reg           adcclk_tmp;
  wire          adcclk;
  wire          adcclk_div1;
  
  wire          ext_mux;
  wire          ext_mux_en;
  wire [5:0]    ext_mux_chan_id;
  wire [5:0]    single_chan_id;
  wire          default_mode;
  wire          single_pass_mode;
  wire          single_pass_active;
  wire          cont_seq_mode;
  wire          single_chan_mode;
  wire          event_driven_mode;
  wire          cont_sampl_mode;
  wire          bipolar_mode;
  reg           single_pass_finished; 
  reg           single_pass_finished_d; 
  wire          single_pass_finished_pe;

  reg           sim_file_flag;
  reg  [7:0]    DADDR_in_lat;
  wire [3:0]    op_mode;
  reg  [3:0]    seq_bits;
  reg           ot_en; 
  reg  [13:0]   alm_en;
  wire [15:0]   seq_hr_chan_reg1;
  wire [15:0]   seq_hr_chan_reg2;
  wire [15:0]   seq_hr_chan_reg3;
  wire [47:0]   seq_hr_chan_reg_comb;
  wire [15:0]   seq_lr_chan_reg1;
  wire [15:0]   seq_lr_chan_reg2;
  wire [15:0]   seq_lr_chan_reg3;
  wire [47:0]   seq_lr_chan_reg_comb;
  wire [15:0]   seq_acq_ext_reg1;
  wire [15:0]   seq_acq_ext_reg2;
  wire [47:0]   seq_acq_ext_reg_comb;
  wire [15:0]   seq_avg_reg1;
  wire [15:0]   seq_avg_reg2; 
  wire [15:0]   seq_avg_reg3;
  wire [15:0]   seq_bipolar_reg1;
  wire [15:0]   seq_bipolar_reg2;
  wire [47:0]   seq_bipolar_reg_comb;
 
  reg [5:0]     seq_curr_i, seq_curr_ia;
  integer       busy_rst_cnt;
  reg [5:0]     si; 
  integer       kk;
  integer       hr_tot_chan;
  integer       lr_tot_chan;
  wire [15:0]   int_tot_per;
  wire [15:0]   hr_lr_tot_per;
  wire [15:0]   tot_per;
  integer       seq_hr_mem [CONV_CNT_P:0];
  integer       seq_lr_mem [CONV_CNT_P:0];

  wire          lr_chan_on;
  wire          cont_seq_only_hr;
  reg           lr_calib_on;

  wire          sysmon_rst;
  wire [15:0]   cfg_reg0;
  wire [15:0]   cfg_reg1;
  wire [15:0]   cfg_reg2;
  wire [15:0]   cfg_reg3;
  wire [15:0]   cfg_reg4;
  reg           reserved_addr_pre;
  reg           read_only_pre;
  //blh tests related
  wire          blh_test=0;
  integer       blh_read_index=0;
  reg           RESERVED_ADDR;
  reg           READ_ONLY;
    
  wire          convst_in_ored;
  wire          convst_in_pre;
  wire          rst_in_not_seq;
  wire          gsr_in;
  reg  [1:0]    lr_eos ;
  reg  [1:0]    lr_rate;

  real          i2c_vpvn_addr_tmp;
  integer       i2c_conv_result_int;
  reg           i2c_en;
  reg           i2c_oride;
  reg  [6:0]    i2c_device_addr;
  reg  [6:0]    i2c_device_addr_vpvn;
  reg  [15:0]   conv_result_i2c_addr;
  wire          i2c_wr_exec;
  wire [15:0]   i2c_drp_data;
  wire [9:0]    i2c_drp_addr;
  wire          pmb_en_bit;
  wire          pmb_en;
  reg  [7:0]    pmb_sel_addr;   //select address for MFR command
  reg  [7 :0]   pmb_drsram_addr;
  reg  [15:0]   pmb_drsram_wr_data;
  reg  [3:0]    pmb_drsram_bit_idx;
  reg  [7:0]    pmb_drsram_addr_page;
  reg           pmb_valid_page;
  reg           pmb_wr_exec;
  reg  [7:0]    pmb_cmd_in;
  reg  [15:0]   pmb_data_in;
  wire [3:0]    bank_sel_6V; //indicates if 6V bank has been selected for vuser0-3.

  assign JTAGBUSY_out     = 0;
  assign JTAGLOCKED_out   = 0;
  assign JTAGMODIFIED_out = 0;
  assign gsr_in           = glblGSR;

  //--------------------------------------------------
  //--------------------------------------------------
  integer       out_counter;
  integer       ed_counter;
  integer       cs_counter;
  integer       cal_counter;

  reg           out_counter_inc;
  reg           ed_counter_inc;
  wire          chan_asrt_1;
  wire          chan_asrt_2;
  wire          chan_asrt_3;
  reg           chan_asrt_4;
  reg           chan_asrt_5;
  reg           chan_asrt_6;
  wire          alm_asrt;
  wire          eoc_asrt;
  wire          busy_start;
  wire          busy_end;
  wire          busy_end_out;
  wire          busy_start_ed;
  wire          busy_start_cs;
  reg           busy_start_cs_d;
  wire          busy_end_ed;
  wire          busy_end_ed_out;
  wire          busy_end_ed_wait;
  wire          busy_end_cs;
  wire          busy_end_cs_out;
  reg           busy_end_d;
  reg           busy_end_out_d;
  wire          busy_end_pe;
  wire          chan_asrt;
  wire          chan_asrt_ed;
  wire          chan_asrt_cs;
  wire          chan_asrt_pe;
  wire          chan_asrt_dclk;
  reg           chan_asrt_d;
  wire          conv_track;
  wire          conv_track_ed;
  wire          conv_track_cs;
  wire          cal_end_level;
  reg           cal_end_level_d;
  wire          cal_end;
  wire          convst_pre_dclk_pe;
  wire          convst_pre_adcclk_pe;
  reg           convst_saved;
  reg           convst_adcclk_d1;   
  reg           convst_adcclk_d2;   
  reg           convst_dclk_d1;   
  reg           one_pass_end;
  wire [3:0]    cal_factor;
  wire [3:0]    cal_factor2;
  wire [8:0]    first_cal_limit;
  wire [8:0]    later_cal_limit;
  wire [5:0]    conv_period;
  wire [4:0]    busy_start_point;
  wire [4:0]    cs_count_tot;
  wire [8:0]    cal_limit;
  reg           conversion_before_calib;
  reg           tot_final_conversion;
  reg           hr_final_conversion;
  reg           lr_final_conversion;

  wire          acq_ext;
  reg           acq_ext_cur;
  reg           acq_ext_cur_d;
  reg           bipolar_cur;
  reg           avg_cur;
  integer       chan_reg_id_cur; // the index number for accessing configuration registers
  integer       chan_out_id_cur; // the number that shows up at the output
  reg           acq_ext_next;
  reg           bipolar_next;
  reg           avg_next;
  integer       chan_reg_id_next;
  integer       chan_out_id_next;

   // initialize chan_val and chan_valn
  integer ii, jj;
  initial begin
    for (ii = 0; ii < CONV_CNT_P; ii = ii + 1) 
      chan_val[ii] = 64'd0;
    for (jj = 0; jj < 36; jj = jj + 1)
      chan_valn[jj] = 64'd0;
   end

   // initialize vauxn_idx and vauxp_idx
  integer mm, nn;
  initial begin
    for (mm = 0; mm < 16; mm = mm + 1) 
      vauxn_idx[mm] = -1;
    for (nn = 0; nn < 16; nn = nn + 1)
      vauxp_idx[nn] = -1;
  end

 
  initial begin
    i2c_en              = 1;
    pmb_sel_addr        = 0;
  end

  // I2C slave address mapping
  always @(*) begin
    i2c_oride       = cfg_reg3[15];
    i2c_device_addr = (i2c_oride) ? cfg_reg3[14:8]: i2c_device_addr_vpvn;
  end

  assign convst_in_ored  = (CONVST_in===1 || CONVSTCLK_in===1) ? 1: 0;
  assign convst_in_pre   = sysmon_rst ? 0 : (convst_in_ored && event_driven_mode & ~BUSY_out);
  
  integer dd;
  always @(posedge trig_attr) begin
    dr_sram[8'h40] = INIT_40_BIN;
    dr_sram[8'h41] = INIT_41_BIN;
    dr_sram[8'h42] = INIT_42_BIN;
    dr_sram[8'h43] = INIT_43_BIN;
    dr_sram[8'h44] = INIT_44_BIN;
    dr_sram[8'h45] = INIT_45_BIN;
    dr_sram[8'h46] = INIT_46_BIN;
    dr_sram[8'h47] = INIT_47_BIN;
    dr_sram[8'h48] = INIT_48_BIN;
    dr_sram[8'h49] = INIT_49_BIN;
    dr_sram[8'h4A] = INIT_4A_BIN;
    dr_sram[8'h4B] = INIT_4B_BIN;
    dr_sram[8'h4C] = INIT_4C_BIN;
    dr_sram[8'h4D] = INIT_4D_BIN;
    dr_sram[8'h4E] = INIT_4E_BIN;
    dr_sram[8'h4F] = INIT_4F_BIN;
    dr_sram[8'h50] = INIT_50_BIN;
    dr_sram[8'h51] = INIT_51_BIN;
    dr_sram[8'h52] = INIT_52_BIN;

    // User can overwrite the ot_limit_reg only while enabling automatic shutdown. 
    // Otherwise default value will be kept.
    tmp_otv = INIT_53_BIN;
    if (tmp_otv [3:0] == 4'b0011) begin 
      dr_sram[8'h53] = INIT_53_BIN;
      ot_limit_reg  = INIT_53_BIN;
      $display("Info: [Unisim %s-20] OT upper limit has been overwritten and automatic shutdown bits have been set 53h = h%0h. Please refer to the Thermal Management section of the User Guide. Instance: %m", MODULE_NAME, INIT_53_BIN, $time/1000.0,);
    end
    else begin
      dr_sram[8'h53] = 16'hCB00; 
      ot_limit_reg   = 16'hCB00;  // default value for OT is 125C  
    end

    dr_sram[8'h54] = INIT_54_BIN;
    dr_sram[8'h55] = INIT_55_BIN;
    dr_sram[8'h56] = INIT_56_BIN;
    dr_sram[8'h57] = INIT_57_BIN;
    dr_sram[8'h58] = INIT_58_BIN;
    dr_sram[8'h59] = INIT_59_BIN;
    dr_sram[8'h5A] = INIT_5A_BIN;
    dr_sram[8'h5B] = INIT_5B_BIN;
    dr_sram[8'h5C] = INIT_5C_BIN;
    dr_sram[8'h5D] = INIT_5D_BIN;
    dr_sram[8'h5E] = INIT_5E_BIN;
    dr_sram[8'h5F] = INIT_5F_BIN;
    dr_sram[8'h60] = INIT_60_BIN;
    dr_sram[8'h61] = INIT_61_BIN;
    dr_sram[8'h62] = INIT_62_BIN;
    dr_sram[8'h63] = INIT_63_BIN;
    dr_sram[8'h68] = INIT_68_BIN;
    dr_sram[8'h69] = INIT_69_BIN;
    dr_sram[8'h6A] = INIT_6A_BIN;
    dr_sram[8'h6B] = INIT_6B_BIN;
    dr_sram[8'h78] = INIT_78_BIN;
    dr_sram[8'h79] = INIT_79_BIN;
    dr_sram[8'h7A] = INIT_7A_BIN;
    dr_sram[8'h7B] = INIT_7B_BIN;
    dr_sram[8'h7C] = INIT_7C_BIN;

    for (dd=8'h80; dd<8'hFF; dd=dd+1)
      dr_sram[dd] = 0;

    dr_sram[8'hA8] = 16'hFFFF; //min vuser0
    dr_sram[8'hA9] = 16'hFFFF;
    dr_sram[8'hAA] = 16'hFFFF;
    dr_sram[8'hAB] = 16'hFFFF;

  end // always @ (trig_attr)
   
   
  // read input file
  initial begin
    char_1 = 0;
    char_2 = 0;
    time_out = 0;
    sim_file_flag = 0;
    file_line = -1;
    end_of_file = 0;
    fd = $fopen(SIM_MONITOR_FILE, "r"); 
    if  (fd == 0)    begin
      $display("Error: [Unisim %s-4] The analog data file %s was not found. Use the SIM_MONITOR_FILE parameter to specify the analog data file name or use the default name: design.txt. Instance: %m", MODULE_NAME, SIM_MONITOR_FILE);
      sim_file_flag = 1;
      #1 $finish;
    end
      
    if (sim_file_flag == 0) begin
      while (end_of_file==0) begin
        file_line = file_line + 1;
        char_1 = $fgetc (fd);
        char_2 = $fgetc (fd);
        //if(char_2==`EOFile) 
        if(char_2== -1) 
          end_of_file = 1;
        else begin // not end of file
          // Ignore Comments
          if ((char_1 == "/" & char_2 == "/") | char_1 == "#" | (char_1 == "-" & char_2 == "-")) begin
            fs = $ungetc (char_2, fd);
            fs = $ungetc (char_1, fd);
            fs = $fgets (one_line, fd);
          end
          // Getting labels
          else if ((char_1 == "T" & char_2 == "I" ) ||
                   (char_1 == "T" & char_2 == "i" ) ||
                   (char_1 == "t" & char_2 == "i" ) || (char_1 == "t" & char_2 == "I" ))  begin
            fs = $ungetc (char_2, fd);
            fs = $ungetc (char_1, fd);
            fs = $fgets (one_line, fd);

            num_arg = $sscanf (one_line, "%s %s %s %s %s %s %s %s %s %s %s %s %s %s %s %s %s %s %s %s %s %s %s %s %s %s %s %s %s %s %s %s %s %s %s %s %s %s %s %s %s %s %s %s %s %s %s ", 
                               label0, label1, label2, label3, label4, label5, label6, label7, label8, label9, label10, label11, label12, label13, label14, label15, label16, label17, label18, label19, label20, label21, label22, label23, label24, label25, label26, label27, label28, label29, label30,label31, label32, label33, label34, label35, label36, label37, label38, label39, label40, label41, label42, label43, label44, label45, label46);
        
            label[0]  = label0;
            label[1]  = label1;
            label[2]  = label2;
            label[3]  = label3;
            label[4]  = label4;
            label[5]  = label5;
            label[6]  = label6;
            label[7]  = label7;
            label[8]  = label8;
            label[9]  = label9;
            label[10] = label10;
            label[11] = label11;
            label[12] = label12;
            label[13] = label13;
            label[14] = label14;
            label[15] = label15;
            label[16] = label16;
            label[17] = label17;
            label[18] = label18;
            label[19] = label19;
            label[20] = label20;
            label[21] = label21;
            label[22] = label22;
            label[23] = label23;
            label[24] = label24;
            label[25] = label25;
            label[26] = label26;
            label[27] = label27;
            label[28] = label28;
            label[29] = label29;
            label[30] = label30;
            label[31] = label31;
            label[32] = label32;
            label[33] = label33;
            label[34] = label34;
            label[35] = label35;
            label[36] = label36;
            label[37] = label37;
            label[38] = label38;
            label[39] = label39;
            label[40] = label40;
            label[41] = label41;
            label[42] = label42;
            label[43] = label43;
            label[44] = label44;
            label[45] = label45;        
            label[46] = label46;
        
            for (m = 0; m < num_arg; m = m +1) begin
              tmp_label = 96'b0;
              tmp_label = to_upcase_label(label[m]);
              case (tmp_label)
                "TEMP"          : temperature_index = m; 
                "TIME"          : time_index = m;
                "VCCAUX"        : vccaux_index = m;
                "VCCINT"        : vccint_index = m;
                "VCCBRAM"       : vccbram_index = m;
                "VCCPSINTLP",     
                "VCC_PSINTLP"   : 
                                  begin 
                                    vccpsintlp_index = m;
                                    if (SIM_DEVICE != "ZYNQ_ULTRASCALE" && 
                                        SIM_DEVICE != "ZYNQ_ULTRASCALE_ES1" && 
                                        SIM_DEVICE != "ZYNQ_ULTRASCALE_ES2")
                                      $display("Error: [Unisim %s-22] The channel name %s is invalid in the input file. Instance: %m", MODULE_NAME, tmp_label);
                                    if ("VCCPSINTLP" == tmp_label)
                                      $display("Error: [Unisim %s-47] The channel name %s is deprecated. Please use VCC_PSINTLP instead. Instance: %m", MODULE_NAME, tmp_label);
                                  end
                "VCCPSINTFP",     
                "VCC_PSINTFP"   : 
                                  begin 
                                    vccpsintfp_index = m;
                                    if (SIM_DEVICE != "ZYNQ_ULTRASCALE" && 
                                        SIM_DEVICE != "ZYNQ_ULTRASCALE_ES1" && 
                                        SIM_DEVICE != "ZYNQ_ULTRASCALE_ES2")
                                      $display("Error: [Unisim %s-23] The channel name %s is invalid in the input file. Instance: %m", MODULE_NAME, tmp_label);
                                    if ("VCCPSINTFP" == tmp_label)
                                      $display("Error: [Unisim %s-48] The channel name %s is deprecated. Please use VCC_PSINTFP instead. Instance: %m", MODULE_NAME, tmp_label);
                                  end
                "VCCPSAUX", 
                "VCC_PSAUX"     : begin 
                                    vccpsaux_index = m;
                                    if (SIM_DEVICE != "ZYNQ_ULTRASCALE" && 
                                        SIM_DEVICE != "ZYNQ_ULTRASCALE_ES1" && 
                                        SIM_DEVICE != "ZYNQ_ULTRASCALE_ES2")
                                      $display("Error: [Unisim %s-24] The channel name %s is invalid in the input file. Instance: %m", MODULE_NAME, tmp_label);
                                    if ("VCCPSAUX" == tmp_label)
                                      $display("Error: [Unisim %s-49] The channel name %s is deprecated. Please use VCC_PSAUX instead. Instance: %m", MODULE_NAME, tmp_label);
                                  end
                "VN"            : vn_index     = m;
                "VAUXN[0]"      : vauxn_idx[0] = m;
                "VAUXN[1]"      : vauxn_idx[1] = m;
                "VAUXN[2]"      : vauxn_idx[2] = m;
                "VAUXN[3]"      : vauxn_idx[3] = m;
                "VAUXN[4]"      : vauxn_idx[4] = m;
                "VAUXN[5]"      : vauxn_idx[5] = m;
                "VAUXN[6]"      : vauxn_idx[6] = m;
                "VAUXN[7]"      : vauxn_idx[7] = m;
                "VAUXN[8]"      : vauxn_idx[8] = m;
                "VAUXN[9]"      : vauxn_idx[9] = m;
                "VAUXN[10]"     : vauxn_idx[10] = m;
                "VAUXN[11]"     : vauxn_idx[11] = m;
                "VAUXN[12]"     : vauxn_idx[12] = m;
                "VAUXN[13]"     : vauxn_idx[13] = m;
                "VAUXN[14]"     : vauxn_idx[14] = m;
                "VAUXN[15]"     : vauxn_idx[15] = m;
                "VP"            : vp_index      = m;
                "VAUXP[0]"      : vauxp_idx[0] = m;
                "VAUXP[1]"      : vauxp_idx[1] = m;
                "VAUXP[2]"      : vauxp_idx[2] = m;
                "VAUXP[3]"      : vauxp_idx[3] = m;
                "VAUXP[4]"      : vauxp_idx[4] = m;
                "VAUXP[5]"      : vauxp_idx[5] = m;
                "VAUXP[6]"      : vauxp_idx[6] = m;
                "VAUXP[7]"      : vauxp_idx[7] = m;
                "VAUXP[8]"      : vauxp_idx[8] = m;
                "VAUXP[9]"      : vauxp_idx[9] = m;
                "VAUXP[10]"     : vauxp_idx[10] = m;
                "VAUXP[11]"     : vauxp_idx[11] = m;
                "VAUXP[12]"     : vauxp_idx[12] = m;
                "VAUXP[13]"     : vauxp_idx[13] = m;
                "VAUXP[14]"     : vauxp_idx[14] = m;
                "VAUXP[15]"     : vauxp_idx[15] = m;
                "VUSER0"        : vuser0_index = m;
                "VUSER1"        : vuser1_index = m;
                "VUSER2"        : vuser2_index = m;
                "VUSER3"        : vuser3_index = m;
                //"VCCAMS"        : vccams_index = m;
                default         : begin
                                    $display("Error: [Unisim %s-5] The channel name %s is invalid in the input file. Instance: %m", MODULE_NAME, tmp_label);
                                    infile_format;
                                  end
              endcase
            end // for (m = 0; m < num_arg; m = m +1)

            // COMMON_N_SOURCE
            if(COMMON_N_SOURCE != 16'hFFFF && vauxn_idx[COMMON_N_SOURCE[3:0]] == -1) begin
              $display("Warning: [Unisim %s-58]: Common-N Source is selected as VAUXN[%0d]. This input does not exist in the stimulus file. It must be provided.",
                MODULE_NAME, COMMON_N_SOURCE[3:0]);
              for (n = 0; n < 16; n = n + 1) begin
                if ((vauxn_idx[n] == -1) && (vauxp_idx[n] != -1))
                  vauxn_idx[n] = vauxn_idx[COMMON_N_SOURCE[3:0]];
                end // for 
            end

          end // Getting labels
          
          // Getting column values
          else if (char_1 ==" " | char_1 == "0" | char_1 == "1" | char_1 == "2" | char_1 == "3" | char_1 == "4" | char_1 == "5" | char_1 == "6" | char_1 == "7" | char_1 == "8" | char_1 == "9") begin
        
            fs = $ungetc (char_2, fd);
            fs = $ungetc (char_1, fd);
            fs = $fgets (one_line, fd);
           
            column_real0 = 0.0;
            column_real1 = 0.0;
            column_real2 = 0.0;
            column_real3 = 0.0;
            column_real4 = 0.0;
            column_real5 = 0.0;
            column_real6 = 0.0;
            column_real7 = 0.0;
            column_real8 = 0.0;
            column_real9 = 0.0;
            column_real10 = 0.0;
            column_real11 = 0.0;
            column_real12 = 0.0;
            column_real13 = 0.0;
            column_real14 = 0.0;
            column_real15 = 0.0;
            column_real16 = 0.0;
            column_real17 = 0.0;
            column_real18 = 0.0;
            column_real19 = 0.0;
            column_real20 = 0.0;
            column_real21 = 0.0;
            column_real22 = 0.0;
            column_real23 = 0.0;
            column_real24 = 0.0;
            column_real25 = 0.0;
            column_real26 = 0.0;
            column_real27 = 0.0;
            column_real28 = 0.0;
            column_real29 = 0.0;
            column_real30 = 0.0;
            column_real31 = 0.0;
            column_real32 = 0.0;
            column_real33 = 0.0;
            column_real34 = 0.0;
            column_real35 = 0.0;
            column_real36 = 0.0;
            column_real37 = 0.0;
            column_real38 = 0.0;
            column_real39 = 0.0;
            column_real40 = 0.0;
            column_real41 = 0.0;
            column_real42 = 0.0;
            column_real43 = 0.0;
            column_real44 = 0.0;
            column_real45 = 0.0;
            column_real46 = 0.0;
           
            num_val = $sscanf (one_line, "%f %f %f %f %f %f %f %f %f %f %f %f %f %f %f %f %f %f %f %f %f %f %f %f %f %f %f %f %f %f %f %f %f %f %f %f %f %f %f %f %f %f %f %f %f %f %f", column_real0, column_real1, column_real2, column_real3, column_real4, column_real5, column_real6, column_real7, column_real8, column_real9, column_real10, column_real11, column_real12, column_real13, column_real14, column_real15, column_real16, column_real17, column_real18, column_real19, column_real20, column_real21, column_real22, column_real23, column_real24, column_real25, column_real26, column_real27, column_real28, column_real29, column_real30, column_real31, column_real32, column_real33, column_real34, column_real35, column_real36, column_real37, column_real38, column_real39, column_real40, column_real41, column_real42, column_real43, column_real44, column_real45, column_real46);

            column_real[0] = $realtobits(column_real0);
            column_real[1] = $realtobits(column_real1);
            column_real[2] = $realtobits(column_real2);
            column_real[3] = $realtobits(column_real3);
            column_real[4] = $realtobits(column_real4);
            column_real[5] = $realtobits(column_real5);
            column_real[6] = $realtobits(column_real6);
            column_real[7] = $realtobits(column_real7);
            column_real[8] = $realtobits(column_real8);
            column_real[9] = $realtobits(column_real9);
            column_real[10] = $realtobits(column_real10);
            column_real[11] = $realtobits(column_real11);
            column_real[12] = $realtobits(column_real12);
            column_real[13] = $realtobits(column_real13);
            column_real[14] = $realtobits(column_real14);
            column_real[15] = $realtobits(column_real15);
            column_real[16] = $realtobits(column_real16);
            column_real[17] = $realtobits(column_real17);
            column_real[18] = $realtobits(column_real18);
            column_real[19] = $realtobits(column_real19);
            column_real[20] = $realtobits(column_real20);
            column_real[21] = $realtobits(column_real21);
            column_real[22] = $realtobits(column_real22);
            column_real[23] = $realtobits(column_real23);
            column_real[24] = $realtobits(column_real24);
            column_real[25] = $realtobits(column_real25);
            column_real[26] = $realtobits(column_real26);
            column_real[27] = $realtobits(column_real27);
            column_real[28] = $realtobits(column_real28);
            column_real[29] = $realtobits(column_real29);
            column_real[30] = $realtobits(column_real30);
            column_real[31] = $realtobits(column_real31);
            column_real[32] = $realtobits(column_real32);
            column_real[33] = $realtobits(column_real33);
            column_real[34] = $realtobits(column_real34);
            column_real[35] = $realtobits(column_real35);
            column_real[36] = $realtobits(column_real36);
            column_real[37] = $realtobits(column_real37);
            column_real[38] = $realtobits(column_real38);
            column_real[39] = $realtobits(column_real39);
            column_real[40] = $realtobits(column_real40);
            column_real[41] = $realtobits(column_real41);
            column_real[42] = $realtobits(column_real42);
            column_real[43] = $realtobits(column_real43);
            column_real[44] = $realtobits(column_real44);
            column_real[45] = $realtobits(column_real45);
            column_real[46] = $realtobits(column_real46);
           
            chan_val[0]   = column_real[temperature_index];
            chan_val[1]   = column_real[vccint_index];
            chan_val[2]   = column_real[vccaux_index];
            chan_val[3]   = column_real[vp_index];
            chan_val[6]   = column_real[vccbram_index];
            chan_val[13]  = column_real[vccpsintlp_index];
            chan_val[14]  = column_real[vccpsintfp_index];
            chan_val[15]  = column_real[vccpsaux_index];
            chan_val[16]  = column_real[vauxp_idx[0]];
            chan_val[17]  = column_real[vauxp_idx[1]];
            chan_val[18]  = column_real[vauxp_idx[2]];
            chan_val[19]  = column_real[vauxp_idx[3]];
            chan_val[20]  = column_real[vauxp_idx[4]];
            chan_val[21]  = column_real[vauxp_idx[5]];
            chan_val[22]  = column_real[vauxp_idx[6]];
            chan_val[23]  = column_real[vauxp_idx[7]];
            chan_val[24]  = column_real[vauxp_idx[8]];
            chan_val[25]  = column_real[vauxp_idx[9]];
            chan_val[26]  = column_real[vauxp_idx[10]];
            chan_val[27]  = column_real[vauxp_idx[11]];
            chan_val[28]  = column_real[vauxp_idx[12]];
            chan_val[29]  = column_real[vauxp_idx[13]];
            chan_val[30]  = column_real[vauxp_idx[14]];
            chan_val[31]  = column_real[vauxp_idx[15]];
            chan_val[32]  = column_real[vuser0_index];
            chan_val[33]  = column_real[vuser1_index];
            chan_val[34]  = column_real[vuser2_index];
            chan_val[35]  = column_real[vuser3_index];
            
            chan_valn[3]  = column_real[vn_index];
            chan_valn[16] = column_real[vauxn_idx[0]];
            chan_valn[17] = column_real[vauxn_idx[1]];
            chan_valn[18] = column_real[vauxn_idx[2]];
            chan_valn[19] = column_real[vauxn_idx[3]];
            chan_valn[20] = column_real[vauxn_idx[4]];
            chan_valn[21] = column_real[vauxn_idx[5]];
            chan_valn[22] = column_real[vauxn_idx[6]];
            chan_valn[23] = column_real[vauxn_idx[7]];
            chan_valn[24] = column_real[vauxn_idx[8]];
            chan_valn[25] = column_real[vauxn_idx[9]];
            chan_valn[26] = column_real[vauxn_idx[10]];
            chan_valn[27] = column_real[vauxn_idx[11]];
            chan_valn[28] = column_real[vauxn_idx[12]];
            chan_valn[29] = column_real[vauxn_idx[13]];
            chan_valn[30] = column_real[vauxn_idx[14]];
            chan_valn[31] = column_real[vauxn_idx[15]];
           
        
            // identify columns
            if (time_index != -1) begin
              prev_time_out = time_out;
              time_out = $bitstoreal(column_real[time_index]);
              if (prev_time_out > time_out) begin
                $display("Error: [Unisim %s-6] Time value %f is invalid in the input file. Time value should be increasing. Instance: %m", MODULE_NAME, time_out);
                infile_format;
              end
            end     
            else begin
              $display("Error: [Unisim %s-7] No TIME label is found in the analog data file. Instance: %m", MODULE_NAME);
              infile_format;
              #1 $finish;
            end

            # ((time_out - prev_time_out) * 1000);

            for (p = 0; p < CONV_CNT_P; p = p + 1) begin
              // assign to real before minus - to work around a bug in modelsim
              chan_val_tmp[p]   = chan_val[p];
              chan_valn_tmp[p]  = chan_valn[p];
              mn_in_tmp         = $bitstoreal(chan_val[p])  - $bitstoreal(chan_valn[p]);
              mn_in_diff[p]     = $realtobits(mn_in_tmp);
              mn_in_uni[p]      = chan_val[p];
            end
          end // if (char_1 == "0" | char_1 == "9")
          // Ignore any non-comment, label
          else begin
            fs = $ungetc (char_2, fd);
            fs = $ungetc (char_1, fd);
            fs = $fgets (one_line, fd);    
          end
        end 
      end // while (end_file == 0)


    end // if (sim_file_flag == 0)
  end // initial begin

  always@(posedge chan_asrt_1) begin
    if(sysmon_rst==0 && blh_test==1) begin
      blh_read_index = chan_out_id_next;
      chan_val_tmp [blh_read_index]  = chan_val[blh_read_index];
      chan_valn_tmp[blh_read_index]  = chan_valn[blh_read_index];
      mn_in_tmp                      =  $bitstoreal(chan_val [blh_read_index])  
                                      - $bitstoreal(chan_valn[blh_read_index]);
      mn_in_diff[blh_read_index]     = $realtobits(mn_in_tmp);
      mn_in_uni[blh_read_index]      = chan_val[blh_read_index];
    end
  end

  // Obtain I2C slave address powerup value
  always @(posedge trig_i2c_addr) begin
    i2c_vpvn_addr_tmp =  $bitstoreal(mn_in_uni[3]) * 65536.0; 
    if (i2c_vpvn_addr_tmp > 65535.0)
      i2c_conv_result_int = 65535;
    else if (i2c_vpvn_addr_tmp < 0.0)
      i2c_conv_result_int = 0;
    else begin
      i2c_conv_result_int = $rtoi(i2c_vpvn_addr_tmp);
      if (i2c_vpvn_addr_tmp - i2c_conv_result_int > 0.9999)
        i2c_conv_result_int = i2c_conv_result_int + 1;
    end
    // I2C address measured and assigned at startup is recorded at address 38h
    conv_result_i2c_addr = i2c_conv_result_int;
    if(!i2c_oride)
      data_reg[56] = i2c_conv_result_int;  
    

    // convert i2c address
    case (conv_result_i2c_addr[15:12])
      4'h0    :   i2c_device_addr_vpvn = 7'b0110010;
      4'h1    :   i2c_device_addr_vpvn = 7'b0001011;
      4'h2    :   i2c_device_addr_vpvn = 7'b0010011;
      4'h3    :   i2c_device_addr_vpvn = 7'b0011011;
      4'h4    :   i2c_device_addr_vpvn = 7'b0100011;
      4'h5    :   i2c_device_addr_vpvn = 7'b0101011;
      4'h6    :   i2c_device_addr_vpvn = 7'b0110011;
      4'h7    :   i2c_device_addr_vpvn = 7'b0111011;
      4'h8    :   i2c_device_addr_vpvn = 7'b1000011;
      4'h9    :   i2c_device_addr_vpvn = 7'b1001011;
      4'ha    :   i2c_device_addr_vpvn = 7'b1010011;
      4'hb    :   i2c_device_addr_vpvn = 7'b1011011;
      4'hc    :   i2c_device_addr_vpvn = 7'b1100011;
      4'hd    :   i2c_device_addr_vpvn = 7'b1101011;
      4'he    :   i2c_device_addr_vpvn = 7'b1110011;
      4'hf    :   i2c_device_addr_vpvn = 7'b0111010;
      default : begin
                  i2c_device_addr_vpvn = 7'b0000000; 
                  //$display("Warning: [Unisim %s-25] Invalid I2C address is found. Instance: %m", MODULE_NAME);
                end
    endcase  
  end

  task infile_format;
    begin
    $display("\n***** SYSMONE4 Simulation analog Data File Format *****\n");
    $display("NAME: design.txt or user file name passed with parameter/generic SIM_MONITOR_FILE\n");
    $display("FORMAT: First line is header line. Valid column name are: TIME TEMP VCCINT VCCAUX VCCBRAM VCC_PSINTLP VCC_PSINTFP VCC_PSAUX VP VN VAUXP[0] VAUXN[0] ..... \n");
    $display("TIME must be in first column.\n");
    $display("Time values need to be integer in ns scale.\n");
    $display("Analog values need to be real and must contain a decimal point '.' ,  e.g. 0.0, 3.0\n");
    $display("Each line including header line can not have extra space after the last character/digit.\n");
    $display("Each data line must have the same number of columns as the header line.\n");
    $display("Comment line can start with -- or //\n");
    $display("Example:\n");
    $display("TIME TEMP VCCINT  VP VN VAUXP[0] VAUXN[0]\n");
    $display("000  125.6  1.0  0.7  0.4  0.3  0.6\n");
    $display("200  25.6   0.8  0.5  0.3  0.8  0.2\n");
    end
  endtask  //task infile_format

  function [12*8:1] to_upcase_label;
    input  [12*8:1] in_label;
    reg [8:1] tmp_reg;
    begin
      for (i=0; i< 12; i=i+1) begin
        for (j=1; j<=8; j= j+1)
          tmp_reg[j] = in_label[i*8+j];
          if ((tmp_reg >96) && (tmp_reg<123))
            tmp_reg = tmp_reg -32;
            for (j=1; j<=8; j= j+1)
              to_upcase_label[i*8+j] = tmp_reg[j];
      end
    end
  endfunction

  // end read input file

  //convert combined register index to channel output
  //or vice-a-versa
  function [5:0] conv_combregid_to_chanout;
    input [5:0] combregid; //unsigned
    begin
      // invalid channel outputs are 7, 9-12, and >=36. They show up as selected via registers
      if(combregid<=7)
        conv_combregid_to_chanout = combregid+8;
      else if(combregid>=8 && combregid<=15)
        conv_combregid_to_chanout = combregid-8;
      else
        conv_combregid_to_chanout = combregid;
    end
  endfunction

  always @(posedge DCLK_in or posedge sysmon_rst ) begin
    if (sysmon_rst==1) 
      MUXADDR_out <= 5'b0;
    else begin
      if(ext_mux_en==0) 
        MUXADDR_out <= 5'b0;
      else if((|initialize) || adc_state==ST_A_FIRST_CALIB || adc_state==ST_A_CALIB)
        MUXADDR_out <= 8; // stay in calibration until first channel conversion
      else if(chan_asrt_6==1 || (CHANNEL_out==8 && busy_end_out_d )) 
        MUXADDR_out <= chan_out_id_next;
    end
  end

  always @(posedge DCLK_in or posedge sysmon_rst) begin
    if(sysmon_rst==1)
      CHANNEL_out <= 8;
    else begin
      if((|initialize) || chan_asrt_6==1) 
        CHANNEL_out <= chan_out_id_cur;
    end
  end
  

  always @(posedge DCLK_in or posedge sysmon_rst) begin
    if(sysmon_rst==1)
      ADC_DATA_out <= 0;
    else if(eoc_asrt==1) begin
      if (chan_out_id_cur >= 32)
        ADC_DATA_out <= dr_sram[chan_out_id_cur + 96];
      else if (chan_out_id_cur >= 0 && chan_out_id_cur <= 31)
        ADC_DATA_out <= data_reg[chan_out_id_cur];   
    end
  end   

  //----------------------------------------------------------------- 
  // internal reset generation
  //----------------------------------------------------------------- 

  initial begin
    alm_rst =  0;
    init_rst = 1;
    if (RESET_in == 1'b1) begin
      @(negedge RESET_in);
    end
    repeat (2) @(posedge DCLK_in);
    init_rst = 0;
    alm_rst =  1;
    repeat (2) @(posedge DCLK_in);
    alm_rst =  0;
  end

  assign int_rst_combined       = init_rst | soft_rst | seq_rst; //all internally generated
  assign #10 int_rst_combined_d = int_rst_combined;
  assign sysmon_rst             = int_rst_sync2 | RESET_in | gsr_in; //combined reset

  initial begin
    int_rst_sync1 = 0;
    int_rst_sync2 = 0;
  end

  //synchronize internally generated reset to adcclk
  always@(posedge adcclk or posedge int_rst_combined_d) begin
    if (int_rst_combined_d) begin
      int_rst_sync1 <= 1;
      int_rst_sync2 <= 1;
    end
    else begin
      int_rst_sync1 <= int_rst_combined_d;
      int_rst_sync2 <= int_rst_sync1;
    end
  end

  always @(posedge sysmon_rst or posedge DCLK_in) begin
    if(sysmon_rst )
      initialize <= 3'b001;
    else
      initialize <= {initialize[1:0],1'b0};
  end



  initial begin
    sysclk = 0;
    adcclk_tmp = 0;
    adcclk_count = -1;
    //for (i = 0; i <=63; i = i +1) begin
    //  conv_acc[i] = 0;
    //end
    DADDR_in_lat = 0;
    //data registers reset
    for (k = 0; k <= 31; k = k + 1) begin
      data_reg[k] = 16'h0000;
    end 
    //min and max registers' reset value assignments
    data_reg[32] = 16'h0000;
    data_reg[33] = 16'h0000;
    data_reg[34] = 16'h0000;
    data_reg[35] = 16'h0000;
    data_reg[36] = 16'hFFFF;
    data_reg[37] = 16'hFFFF;
    data_reg[38] = 16'hFFFF;
    data_reg[39] = 16'hFFFF;
    data_reg[40] = 16'h0000;
    data_reg[41] = 16'h0000;
    data_reg[42] = 16'h0000;
    data_reg[43] = 16'h0000; //reserved
    data_reg[44] = 16'hFFFF;
    data_reg[45] = 16'hFFFF;
    data_reg[46] = 16'hFFFF;
    data_reg[47] = 16'h0000; //reserved

    ot_out_reg = 0;
    OT_out = 0;
    alm_out_reg = 0;
    ALM_out = 0;
    hr_tot_chan = 0;
    lr_tot_chan = 0;
    ot_en = 1;
    alm_en = 13'h1FFF;
    DO_out_rdtmp = 0;
    conv_result_int = 0;
    conv_result = 0;
    conv_result_reg = 0;
    READ_ONLY     = 0;
    reserved_addr_pre = 0;
    lr_calib_on       = 0;
  end //end of initial

  //----------------------------------------------------------------
  // ADC state machine
  // to manage timing of output ports CHANNEL, BUSY, EOC, EOS, ALM
  //----------------------------------------------------------------
  always @(*) begin
    if(sysmon_rst || (|initialize))
        adc_next_state<= ST_A_FIRST_CALIB;
    else begin
      case (adc_state)
        ST_A_FIRST_CALIB : if(cont_sampl_mode && cal_end && !single_pass_finished)
                             adc_next_state <= ST_A_CHAN;
                           else if(event_driven_mode && cal_end)
                             adc_next_state <= ST_A_WAIT_ED;
        ST_A_CALIB       : if(cont_sampl_mode && cal_end && !single_pass_mode)
                             adc_next_state <= ST_A_CHAN;
                           else if(event_driven_mode && cal_end) begin
                             if(convst_pre_adcclk_pe)
                               adc_next_state <= ST_A_CHAN;
                             else
                               adc_next_state <= ST_A_WAIT_ED;
                           end
        ST_A_WAIT_ED     : if(convst_pre_adcclk_pe) 
                             adc_next_state <= ST_A_WAIT;
        ST_A_WAIT        : if(cont_sampl_mode && single_pass_mode && hr_final_conversion && acq_ext_cur) begin
                             if(BUSY_out)
                               adc_next_state <= ST_A_FIRST_CALIB;
                             else
                               adc_next_state <= ST_A_WAIT;
                           end
                           else if(conversion_before_calib && !single_chan_mode && chan_asrt_dclk )
                             adc_next_state <= ST_A_CALIB;
                           else if(chan_asrt_dclk)
                             adc_next_state <= ST_A_CHAN;
        ST_A_CHAN        : if(convst_pre_adcclk_pe )
                             adc_next_state <= ST_A_WAIT;
                           else if (alm_asrt)
                             adc_next_state <= ST_A_ALM;
        ST_A_ALM         :  if(convst_pre_adcclk_pe )
                             adc_next_state <= ST_A_WAIT;
                           else if(eoc_asrt)
                             adc_next_state <= ST_A_EOC;
        ST_A_EOC         :  if(convst_pre_adcclk_pe )
                             adc_next_state <= ST_A_WAIT;
                           else if(cont_sampl_mode && single_pass_mode && hr_final_conversion && !acq_ext_cur)
                             adc_next_state <= ST_A_FIRST_CALIB;
                           else if (event_driven_mode) 
                             adc_next_state <= ST_A_WAIT_ED;
                           else
                             adc_next_state <= ST_A_WAIT;
        default          : adc_next_state <= ST_A_FIRST_CALIB;
      endcase
    end
  end

  always @(posedge DCLK_in or posedge sysmon_rst) begin
    if(sysmon_rst)
      adc_state <= ST_A_FIRST_CALIB;
    else
      adc_state <= adc_next_state;
  end
   
  always @(posedge DCLK_in or posedge sysmon_rst) begin
    if(sysmon_rst)
      adc_state_d_dclk <= ST_A_FIRST_CALIB;
    else
      adc_state_d_dclk <= adc_state;
  end
   
  always @(posedge adcclk or posedge sysmon_rst) begin
    if(sysmon_rst) 
      adc_state_d  = ST_A_FIRST_CALIB;
    else begin
      #1;
      adc_state_d  = adc_state;
    end
  end

  // signal to stay high until the end of the first ST_A_CHAN 
  always @(posedge DCLK_in or posedge sysmon_rst) begin
    if(sysmon_rst)
      st_first_calib_chan <=1;
    else begin
      if(adc_state==ST_A_CHAN && adc_next_state!=ST_A_CHAN) 
        st_first_calib_chan <=0;
    end
  end

  assign chan_asrt_1    = chan_asrt_pe;
  assign #1 chan_asrt_2 = chan_asrt_1;
  assign #1 chan_asrt_3 = chan_asrt_2;
  assign alm_asrt       = (out_counter == alm_distance) && !(adc_state==ST_A_CALIB || adc_state==ST_A_FIRST_CALIB);
  assign eoc_asrt       = (out_counter == eoc_distance) && !(adc_state==ST_A_CALIB || adc_state==ST_A_FIRST_CALIB);

  always @(posedge DCLK_in or posedge sysmon_rst) begin
    if(sysmon_rst) begin
      chan_asrt_4 <= 0;
      chan_asrt_5 <= 0;
      chan_asrt_6 <= 0;
    end
    else begin
      chan_asrt_4 <= chan_asrt_3;
      chan_asrt_5 <= chan_asrt_4;
      chan_asrt_6 <= busy_end_pe;
    end
  end

  always @(posedge DCLK_in or posedge sysmon_rst) begin
    if(sysmon_rst)
      out_counter <= 0;
    else begin
      if(chan_asrt_dclk || 
         (cal_end && (adc_state==ST_A_CALIB || adc_state==ST_A_FIRST_CALIB)) || 
          out_counter == eoc_distance)
        out_counter <= 0;
      else if(out_counter_inc)// && adc_state!=ST_A_CALIB)
        out_counter <= out_counter + 1;
    end
  end

  always @(posedge DCLK_in or posedge sysmon_rst) begin
    if(sysmon_rst)
      out_counter_inc <=0;
    else begin
      if (chan_asrt_dclk)
        out_counter_inc <=1;
      else if(out_counter == eoc_distance-1)
        out_counter_inc <=0;
    end
  end
          
  //acquisition extension
  assign acq_ext = cfg_reg0[8];

  //event driven mode busy generation
  assign busy_start_ed    = (ed_counter == 1 &&  adc_state!=ST_A_FIRST_CALIB && adc_state!=ST_A_CALIB);
  assign busy_end_ed      = (ed_counter == 22 || (busy_end_ed_wait && ~convst_saved)); //&&first calib or calib might be better.
  assign busy_end_ed_out  = (busy_end_ed &&  adc_state!=ST_A_FIRST_CALIB && adc_state!=ST_A_CALIB);
  assign chan_asrt_ed     = (ed_counter == 21); 
  assign conv_track_ed    = ((ed_counter == 0||ed_counter==22) && CHANNEL_out!=8 );
  assign busy_end_ed_wait = (adc_state == ST_A_WAIT_ED && adc_state_d_dclk != ST_A_WAIT_ED);

  always @(posedge adcclk or posedge sysmon_rst or posedge convst_pre_dclk_pe) begin
    if(sysmon_rst || convst_pre_dclk_pe)
      ed_counter <= 0;
    else begin
      if(!ed_counter_inc || adc_state_d==ST_A_FIRST_CALIB || adc_state_d==ST_A_CALIB || adc_state==ST_A_WAIT_ED ) 
        ed_counter <= 0;
      else if(ed_counter_inc)
        ed_counter <= ed_counter + 1;
    end
  end


  always @(posedge sysmon_rst or posedge DCLK_in) begin
    if(sysmon_rst)
      ed_counter_inc <=0;
    else begin
      if(convst_pre_adcclk_pe && !(adc_state_d==ST_A_FIRST_CALIB || adc_state_d==ST_A_CALIB))
        ed_counter_inc <=1;
      else if(ed_counter==22)
        ed_counter_inc <=0;
    end
  end

  //continuous sampling mode busy generation
  assign busy_start_point= (acq_ext_cur_d) ? 5'd10 : 5'd4;
  assign cs_count_tot    = (acq_ext_cur_d) ? 5'd31 : 5'd25;
  assign busy_start_cs   = (cs_counter == busy_start_point &&  adc_state!=ST_A_FIRST_CALIB && adc_state!=ST_A_CALIB) ||
                           (cal_counter==4 && adc_state==ST_A_CALIB) ;
  assign busy_end_cs     = (cs_counter == 0 &&  adc_state!=ST_A_FIRST_CALIB );
  assign busy_end_cs_out = (cs_counter == 0 &&  adc_state!=ST_A_FIRST_CALIB && adc_state!=ST_A_CALIB);
  assign chan_asrt_cs    = (cs_counter == cs_count_tot);
  assign conv_track_cs   = (cs_counter == 0 && adc_state==ST_A_CHAN);


  always @(posedge adcclk or posedge sysmon_rst) begin
    if(sysmon_rst) begin
      cs_counter <= 0;
      acq_ext_cur_d <=0;
    end
    else begin
      if(cs_counter==cs_count_tot || adc_state==ST_A_FIRST_CALIB || adc_state==ST_A_CALIB) begin
        cs_counter <= 0;
        acq_ext_cur_d <= acq_ext_cur;
      end
      else if(cs_counter < cs_count_tot)
        cs_counter <= cs_counter + 1;
    end
  end

  assign busy_start   = initialize[2] || (event_driven_mode && busy_start_ed) || (~event_driven_mode && busy_start_cs_d);
  assign busy_end     = (event_driven_mode && busy_end_ed)    || (~event_driven_mode && busy_end_cs);
  assign busy_end_out = (event_driven_mode && busy_end_ed_out)|| (~event_driven_mode && busy_end_cs_out);

  always @(posedge DCLK_in or posedge sysmon_rst) begin
    if(sysmon_rst)
      BUSY_out <= 0;
    else begin
      if(busy_start)
        BUSY_out <= 1;
      else if (busy_end_out)
        BUSY_out <= 0;
    end
  end

  assign chan_asrt      = (event_driven_mode && chan_asrt_ed)  || (~event_driven_mode && chan_asrt_cs);
  assign chan_asrt_pe   = chan_asrt & ~chan_asrt_d;
  assign chan_asrt_dclk = (curr_clkdiv_sel>2) ? (chan_asrt & adcclk_period_end_d) : (chan_asrt & chan_asrt_d) ;
  assign busy_end_pe    = busy_end & ~busy_end_d;
  assign conv_track     = event_driven_mode ? conv_track_ed : conv_track_cs;

  always @(posedge DCLK_in or posedge sysmon_rst) begin
    if(sysmon_rst) begin
      chan_asrt_d       <= 0;
      busy_start_cs_d   <= 0;
      busy_end_d        <= 0;
      busy_end_out_d        <= 0;
    end
    else begin 
      chan_asrt_d       <= chan_asrt;
      busy_start_cs_d   <= busy_start_cs;
      busy_end_d        <= busy_end;
      busy_end_out_d    <= busy_end_out;
    end
  end

  
  // BUSY should assert 1 dclk cycle after next adcclk posedge after convst_in_pre
  assign convst_pre_adcclk_pe = convst_in_pre & ~convst_adcclk_d2;
  assign convst_pre_dclk_pe   = convst_in_pre & ~convst_dclk_d1;

  always @(posedge adcclk or posedge sysmon_rst) begin
    if(sysmon_rst) begin
      convst_adcclk_d1 <= 0;
      convst_adcclk_d2 <= 0;
    end
    else begin
      convst_adcclk_d1 <= convst_in_pre ;
      convst_adcclk_d2 <= convst_adcclk_d1 ;
    end
  end

  always @(posedge DCLK_in or posedge sysmon_rst) begin
    if(sysmon_rst) 
      convst_dclk_d1 <= 0;
    else 
      convst_dclk_d1 <= convst_in_pre;
  end

  always @(posedge DCLK_in or posedge sysmon_rst) begin
    if(sysmon_rst) begin
      convst_saved <= 0;
    end
    else begin
      if(convst_pre_adcclk_pe && (adc_state==ST_A_CHAN || adc_state==ST_A_ALM))
        convst_saved <= 1;
      else if (adc_state==ST_A_WAIT || busy_end)
        convst_saved <= 0;
    end
  end


  // Calibration timing
  // calibration period in effect is cal_factor * conversion period
  assign cal_factor      = single_chan_mode? 1: 3; // short calibration for single channel mode to mimick coming out of reset
  assign cal_factor2     = 3;
  assign conv_period     = event_driven_mode ? 22 : (26+(acq_ext_cur_d ? 6 : 0)) ;
  assign first_cal_limit = (cal_factor -1)*conv_period +1; 
  assign later_cal_limit = (cal_factor2-1)*conv_period +2;
  assign cal_limit       = (adc_state==ST_A_FIRST_CALIB) ? first_cal_limit : later_cal_limit; 

  assign cal_end_level     = (cal_counter==cal_limit-1) && BUSY_out; 
  //assign cal_end_pre     = (cal_counter==cal_limit-2); 
  assign cal_end           = cal_end_level && ~cal_end_level_d;         

  always @(posedge adcclk or posedge sysmon_rst) begin
    if(sysmon_rst)
      cal_counter <= 0;
    else begin
      if((conversion_before_calib && busy_end && adc_state!=ST_A_CALIB ) || adc_state==ST_A_WAIT_ED || adc_state==ST_A_WAIT)
        cal_counter <= 0;
      else if((adc_state==ST_A_FIRST_CALIB || adc_state==ST_A_CALIB) && cal_counter <= cal_limit-1 && BUSY_out)
        cal_counter <= cal_counter + 1;
    end
  end

  always @(posedge adcclk or posedge sysmon_rst) begin
    if(sysmon_rst)
      cal_end_level_d <= 0;
    else 
      cal_end_level_d <= cal_end_level;
  end

  //-----------------------------------------------------------------------
  // DRPORT - SRAM
  //-----------------------------------------------------------------------
  initial begin
    DRDY_out = 0;
    DRDY_out_pre1 = 0;
    DRDY_out_pre2 = 0;
    DRDY_out_pre3 = 0;
    en_data_flag = 0;
    DO_out = 16'b0;
  end

//  always @(posedge DRDY_out_pre3 or posedge gsr_in) begin
  always @(DRDY_out_pre3 or posedge gsr_in) begin
    if (gsr_in == 1) 
      DRDY_out <= 0;
//      DRDY_out <= DRDY_out_pre3; // temp
    else begin
//    else if (DRDY_out_pre3) begin // temp
      @(posedge DCLK_in)
        DRDY_out  <= 1;
      @(posedge DCLK_in)
        DRDY_out <= 0;
    end
  end

  function is_reserved_address;
    input [7:0] address_in;
    reg         is_reserved_address_pre;
    begin

    is_reserved_address_pre = ( address_in == 8'h07 || 
                               (address_in >= 8'h0B && address_in <= 8'h0C) ||
                                address_in == 8'h2B || 
                               (address_in >= 8'h2F && address_in <= 8'h37) ||
                               (address_in >= 8'h39 && address_in <= 8'h3D) ||
                                address_in == 8'h45 ||
                               (address_in >= 8'h64 && address_in <= 8'h67) ||
                               (address_in >= 8'h6C && address_in <= 8'h79) || 
                               (address_in >= 8'h7D && address_in <= 8'h7F) ||
                               (address_in >= 8'h84 && address_in <= 8'h9F) ||
                               (address_in >= 8'hA4 && address_in <= 8'hA7) ||
                               (address_in >= 8'hAC && address_in <= 8'hFF)   
                              ); 
    if(is_reserved_address_pre)
      $display("Warning: [Unisim %s-11] The input address=h%x at time %.3f ns is accessing a RESERVED location. The data in this location is invalid. Instance: %m", MODULE_NAME, address_in, $time/1000.0);
    is_reserved_address = is_reserved_address_pre;
  end
  endfunction

  function is_readonly_address;
    input [7:0] address_in;
    reg         is_readonly_address_pre;
    begin

    is_readonly_address_pre = ((address_in <= 8'h02) || // poke hole at 03 CR 993584
                               (address_in >= 8'h04 && address_in <= 8'h3F) ||
                               (address_in >= 8'h80 && address_in <= 8'hAB)  
                              ); 
    if(is_readonly_address_pre)
      $display("Warning: [Unisim %s-19] The input address=h%x at time %.3f ns is accessing a READ ONLY location. The data won't be written. Instance: %m", MODULE_NAME, address_in, $time/1000.0);
    is_readonly_address = is_readonly_address_pre;
    end
  endfunction

  always @(posedge DCLK_in or posedge gsr_in) begin
    if (gsr_in == 1) begin
      DADDR_in_lat      <= 8'b0;
      DO_out            <= 16'b0;
      read_only_pre     <= 0;
      READ_ONLY         <= 0;
      RESERVED_ADDR     <= 0;
//      DRDY_out_pre1 <= DEN_in; // temp
//      DRDY_out_pre2 <= DRDY_out_pre1; // temp
//      DRDY_out_pre3 <= DRDY_out_pre2; // temp
    end
    else  begin
      if (DEN_in == 1'b1) begin
        read_only_pre   <= 0;
        if (DRDY_out_pre1 == 1'b0) begin
          DRDY_out_pre1     <= 1'b1;
          en_data_flag      = 1;
          DADDR_in_lat      <= DADDR_in;
        end
        else 
          $display("Warning: [Unisim %s-10] Input pin DEN can be high for 1 DCLK cycle only. Please wait for DRDY to be high for setting DEN to high again. Instance: %m, time: %.3f ns", MODULE_NAME, $time/1000.0);  
      end // if (DEN_in == 1'b1)
      else
        DRDY_out_pre1 <= 1'b0;

      DRDY_out_pre2 <= DRDY_out_pre1;
      DRDY_out_pre3 <= DRDY_out_pre2;

      if (DRDY_out_pre1 == 1)
        en_data_flag = 0;

      if (DRDY_out_pre3 == 1) begin
        RESERVED_ADDR   <= reserved_addr_pre;
        READ_ONLY       <= read_only_pre;
        if(DWE_in==0) begin
          DO_out            <= DO_out_rdtmp;
        end
      end

      if (DEN_in == 1 && is_reserved_address(DADDR_in) )
        reserved_addr_pre <= 1;
      else if (DWE_in == 1'b1 && DEN_in == 1'b1 && en_data_flag == 1) begin
        //write to all available and writable addresses.
        //check write access
        if (is_readonly_address(DADDR_in))
          read_only_pre <= 1;
        else begin
          read_only_pre <= 0;
          if (DADDR_in != 8'h03) begin // no dr_sram at addr 3
            dr_sram[DADDR_in] <= DI_in;
          end 
        end // not read only
      end // dwe ==1          

      // CR-764936 in event driven mode, when doing one pass when a CONVST BUSY should assert and then an EOC be seen, 
      // the user can assert a CONVST again without having to write to the sequence register to start the sequence again.
      // if continuous sampling, after one pass, the sequencer goes to single channel mode.
      if(single_pass_finished_pe && !event_driven_mode) begin
        dr_sram[8'h41][15:12] <= SEQ_SINGLE_CHAN ;//4'b0011; //from single pass, go to single channel 
      end

    end // if (gsr == 1)
  end //always

  reg        post_process; 
  reg [7:0]  cfg_check_addr;
  reg [15:0] cfg_in;

  //post processing generalized.
  always @(posedge DCLK_in or posedge gsr_in) begin
    if(gsr_in) begin
      post_process   <= 0;
      cfg_check_addr <= 0;
      cfg_in         <= 0;
    end
    else begin 
      if(initialize[2]) begin
        post_process      <= 0;
        cfg_check_addr    <= 0;
        cfg_in            <= 0;
      end
      else if(DEN_in && DWE_in) begin 
        post_process   <= 1;
        cfg_check_addr <= DADDR_in;
        cfg_in         <= DI_in;
      end
      else if(i2c_wr_exec) begin
        post_process   <= 1;
        cfg_check_addr <= i2c_drp_addr[7:0];
        cfg_in         <= i2c_drp_data;
      end
      else if(pmb_wr_exec && pmb_cmd_in==CMD_MFR_ACCESS_REG) begin
        post_process   <= 1;
        cfg_check_addr <= pmb_sel_addr;
        cfg_in         <= pmb_data_in;
      end
      else begin
        post_process   <= 0;
        cfg_check_addr <= 0;
        cfg_in         <= 0;
      end
    end
  end //always

  //post processing generalized.
  always @(posedge DCLK_in or posedge gsr_in) begin
    if (gsr_in == 1) begin
      soft_rst <= 0;
    end
    else  begin
      if(post_process)  begin   
        if (cfg_check_addr == 8'h03)
          soft_rst <= 1;
        else if ( cfg_check_addr == 8'h53 && cfg_in[3:0] == 4'b0011) 
          ot_limit_reg <= cfg_in;// overwrite the OT upper limit 
      end

      if (soft_rst == 1)
        soft_rst <= 0;
    end
  end//always

  always @(posedge post_process) begin
    if(cfg_check_addr == 8'h40) 
      if (cfg_reg0[5:0] == 6'd7 || (cfg_reg0[5:0] >= 6'd9 && cfg_reg0[5:0] <= 6'd12) || cfg_reg0[5:0] >= 6'd36)
        $display("Warning: [Unisim %s-14] Config register 0 bits [5:0] at 40h cannot not be set to an invalid analog channel value as %0b. Instance: %m", MODULE_NAME, cfg_reg0[5:0], $time/1000.0,);
    if(cfg_check_addr == 8'h40 || cfg_check_addr==8'h41) 
      if ((cfg_reg1[15:12]==SEQ_SINGLE_CHAN) && (cfg_reg0[8]==1) && (cfg_reg0[5:0] != 6'd3) && !(cfg_reg0[5:0] >= 6'd16 && cfg_reg0 <= 31))
        $display("Warning: [Unisim %s-15] In single channel mode if the selected channel is not analog, config register 0 bit[8] must be set to 0. Long acqusition mode is only allowed for external channels, not in single channel mode. Instance: %m", MODULE_NAME, DI_in, DADDR_in, $time/1000.0);
    if(cfg_check_addr==8'h41|| cfg_check_addr==8'h46|| cfg_check_addr==8'h48|| cfg_check_addr==8'h49) 
      if ((cfg_reg1[15:12]==SEQ_SINGLE_CHAN) && (seq_hr_chan_reg1 != 16'h0000) && (seq_hr_chan_reg2 != 16'h0000) && (seq_hr_chan_reg3 != 16'h0000))
        $display("Info: [Unisim %s-16] In single channel mode, ADC channel selection registers 46h, 48h and 49h will be ignored; these are set to %x, %x and %x respectively. Instance: %m", MODULE_NAME, seq_hr_chan_reg3, seq_hr_chan_reg1, seq_hr_chan_reg2, $time/1000.0);
    if(cfg_check_addr==8'h41|| cfg_check_addr==8'h7A|| cfg_check_addr==8'h7B|| cfg_check_addr==8'h7C) 
      if ((cfg_reg1[15:12]!=SEQ_CONT_CHAN) && (seq_lr_chan_reg1 != 16'h0000) && (seq_lr_chan_reg2 != 16'h0000) && (seq_lr_chan_reg3 != 16'h0000))
        $display("Info: [Unisim %s-13] In modes other than continuous sequence mode, ADC slow rate channel selection registers 7Ah, 7Bh and 7Ch will be ignored; these are set to %x, %x and %x respectively. Instance: %m", MODULE_NAME, seq_lr_chan_reg3, seq_lr_chan_reg1, seq_lr_chan_reg2, $time/1000.0);
    if(cfg_check_addr == 8'h4E || cfg_check_addr==8'h41) 
      if ((cfg_reg1[15:12]!=SEQ_SINGLE_CHAN) && ((dr_sram['h4E][10:0]!=11'd0) || (dr_sram['h4E][15:12]!=4'd0)))
        $display("Info: [Unisim %s-18] The Control Register 4Eh value set is to %x.  Bits [15:12] and [10:0] of this register will be ignored. Long acquistion mode is only allowed for external channels. Instance: %m", MODULE_NAME, dr_sram['h4E], $time/1000.0);
    if(cfg_check_addr == 8'h42) 
      if (cfg_reg2[4:0]!=5'd0) 
        $display("Warning: [Unisim %s-12] The config reg 2 =h%x is invalid. Bit [4:0] must be set to 5'b00000. Instance: %m", MODULE_NAME, cfg_reg2, $time/1000.0);
    if(cfg_check_addr == 8'h40)
      if(cfg_reg0[13:12]!=2'b00 && !avg_en  ) 
        $display("Info: [Unisim %s-61] When cfg_reg0[13:12] is set to have averaging on: Single pass mode doesn't allow it. Continuous mode needs to have at least one channel in the high rate or low rate sequence needs to have averaging enabled. Otherwise averaging is disabled. Instance: %m", MODULE_NAME, $time/1000.0);
    if(cfg_check_addr == 8'h4C || cfg_check_addr==8'h41) 
      if ((cfg_reg1[15:12]!=SEQ_SINGLE_CHAN) && ((dr_sram['h4C][10:0]!=11'd0) || (dr_sram['h4C][15:12]!=4'd0)))
        $display("Info: [Unisim %s-17] The Control Register 4Ch value set is to %x.  Bits [15:12] and [10:0] of this register will be ignored. Bipolar mode is only allowed for external channels. Instance: %m", MODULE_NAME, dr_sram['h4E], $time/1000.0);
    if(cfg_check_addr == 8'h53)
      if(cfg_in[3:0]==4'b0011)
        $display("Info: [Unisim %s-20] OT upper limit has been overwritten and automatic shutdown bits have been set by input h%0h. Please refer to the Thermal Management section of the User Guide. Instance: %m", MODULE_NAME, cfg_in, $time/1000.0,);
      else // cfg_in[3:0] != 4'b0011
        $display("Info: [Unisim %s-21] OT upper limit can only be overwritten while enabling automatic shutdown, hence input value h%0h will be ignored and the default value will be kept. Please refer to the Thermal Management section of the User Guide. Instance: %m", MODULE_NAME, cfg_in, $time/1000.0,);
    if(cfg_check_addr == 8'h4A)
      if(cfg_in[13:12]!=2'b00 || cfg_in[0]  ) 
        $display("Info: [Unisim %s-26] Calibration, VREFP, and VREFN channels do not allow averaging. Some or all of the bits 0,12,13 of 4A are set to 1 and they will be ignored. Instance: %m", MODULE_NAME, $time/1000.0);
        
  end // post_process


  initial begin
    seq_rst = 0;
  end
  
  always @(posedge DCLK_in or posedge sysmon_rst) begin
    if(sysmon_rst==1)
        seq_rst <= 1'b0;
    else begin
      if((single_pass_finished_pe && ~event_driven_mode) || //single pass finished
         (DWE_in==1 && DEN_in==1 && DADDR_in==8'h41 && (DI_in[15:12]!=cfg_reg1[15:12]) ) || // switching to a different operating mode
         (i2c_wr_exec && i2c_drp_addr==10'h41 && i2c_drp_data[15:12]!=cfg_reg1[15:12]) ||
         (pmb_wr_exec &&  pmb_cmd_in==CMD_MFR_ACCESS_REG && pmb_sel_addr==8'h41 && pmb_data_in[15:12]!=cfg_reg1[15:12]) ||
         (single_chan_mode  && DWE_in==1 && DEN_in==1 && DADDR_in==8'h40 && (DI_in[5:0] != cfg_reg0[5:0]) ) || //change the channel selection in single channel mode
         (i2c_wr_exec && i2c_drp_addr==10'h40 && i2c_drp_data[5:0]!=cfg_reg0[5:0]) ||
         (pmb_wr_exec && pmb_cmd_in==CMD_MFR_ACCESS_REG && pmb_sel_addr==8'h40 && pmb_data_in[5:0]!=cfg_reg0[5:0]) ||
         (pmb_wr_exec && pmb_cmd_in==CMD_PAGE)  //page command adds a new channel to the sequence hence the reset
        )
        seq_rst <= 1'b1;
      else
        seq_rst <= 1'b0;
    end 
  end //always

  // If user adds a new channel to the sequences, then it will be 
  // added after the EOS of the last 
  always @(posedge DCLK_in or posedge sysmon_rst) begin
    if(sysmon_rst==1) begin
        add_channel_hr_p <= 1'b0;
        add_channel_lr_p <= 1'b0;
    end
    else begin
      if((DWE_in==1 && DEN_in==1 && DADDR_in==8'h48 && DI_in!=seq_hr_chan_reg1  ) ||
         (i2c_wr_exec && i2c_drp_addr==10'h48 && i2c_drp_data!=seq_hr_chan_reg1 ) ||
         (pmb_wr_exec &&  pmb_cmd_in==CMD_MFR_ACCESS_REG && pmb_sel_addr==8'h48 && pmb_data_in!=seq_hr_chan_reg1) ||
         (DWE_in==1 && DEN_in==1 && DADDR_in==8'h49 && DI_in!=seq_hr_chan_reg2  ) ||
         (i2c_wr_exec && i2c_drp_addr==10'h49 && i2c_drp_data!=seq_hr_chan_reg2 ) ||
         (pmb_wr_exec &&  pmb_cmd_in==CMD_MFR_ACCESS_REG && pmb_sel_addr==8'h49 && pmb_data_in!=seq_hr_chan_reg2) ||
         (DWE_in==1 && DEN_in==1 && DADDR_in==8'h46 && DI_in!=seq_hr_chan_reg3  ) ||
         (i2c_wr_exec && i2c_drp_addr==10'h46 && i2c_drp_data!=seq_hr_chan_reg3 ) ||
         (pmb_wr_exec &&  pmb_cmd_in==CMD_MFR_ACCESS_REG && pmb_sel_addr==8'h46 && pmb_data_in!=seq_hr_chan_reg3) 
       ) 
        add_channel_hr_p <= 1;
      else if(add_channel)
        add_channel_hr_p <= 0;
      

      if((DWE_in==1 && DEN_in==1 && DADDR_in==8'h7A && DI_in!=seq_lr_chan_reg1  ) ||
         (i2c_wr_exec && i2c_drp_addr==10'h7A && i2c_drp_data!=seq_lr_chan_reg1 ) ||
         (pmb_wr_exec &&  pmb_cmd_in==CMD_MFR_ACCESS_REG && pmb_sel_addr==8'h7A && pmb_data_in!=seq_lr_chan_reg1) ||
         (DWE_in==1 && DEN_in==1 && DADDR_in==8'h7B && DI_in!=seq_lr_chan_reg2  ) ||
         (i2c_wr_exec && i2c_drp_addr==10'h7B && i2c_drp_data!=seq_lr_chan_reg2 ) ||
         (pmb_wr_exec &&  pmb_cmd_in==CMD_MFR_ACCESS_REG && pmb_sel_addr==8'h7B && pmb_data_in!=seq_lr_chan_reg2) ||
         (DWE_in==1 && DEN_in==1 && DADDR_in==8'h7C && DI_in!=seq_lr_chan_reg3  ) ||
         (i2c_wr_exec && i2c_drp_addr==10'h7C && i2c_drp_data!=seq_lr_chan_reg3 ) ||
         (pmb_wr_exec &&  pmb_cmd_in==CMD_MFR_ACCESS_REG && pmb_sel_addr==8'h7C && pmb_data_in!=seq_lr_chan_reg3) 
       ) 
        add_channel_lr_p <= 1;
      else if(add_channel)
        add_channel_lr_p <= 0;

    end 
  end //always



  // DO bus data out

  assign flag_reg0 = {8'b0,  ALM_out[6:3], OT_out, ALM_out[2:0]};
  assign flag_reg1 = {10'b0, ALM_out[13:8]};

  always @(posedge DCLK or posedge gsr_in ) begin
    if(gsr_in==1 ) 
      DO_out_rdtmp <= 0;
    else if(DRDY_out_pre2) begin
      reserved_addr_pre = is_reserved_address(DADDR_in_lat);
      if(reserved_addr_pre)
          DO_out_rdtmp <= 0;
      else begin //readable addresses
        if (DADDR_in_lat <= 8'h3D) 
          DO_out_rdtmp <= data_reg[DADDR_in_lat];
        else if (DADDR_in_lat == 8'h3E)
          DO_out_rdtmp <= flag_reg1;
        else if (DADDR_in_lat == 8'h3F)
          DO_out_rdtmp <= flag_reg0;
        else begin
          DO_out_rdtmp <= dr_sram[DADDR_in_lat];
        end
      end
    end
  end

  //-----------------------------------------------------------------------
  // END of DRPORT - SRAM
  //-----------------------------------------------------------------------


  //-----------------------------------------------------------------------
  // Configuration and settings
  //-----------------------------------------------------------------------
  assign cfg_reg0             = dr_sram[8'h40];
  assign cfg_reg1             = dr_sram[8'h41];
  assign cfg_reg2             = dr_sram[8'h42];
  assign cfg_reg3             = dr_sram[8'h43];
  assign cfg_reg4             = dr_sram[8'h44];
  assign seq_hr_chan_reg1     = dr_sram[8'h48] & 16'h7FE1; //ignore reserved bits
  assign seq_hr_chan_reg2     = dr_sram[8'h49];
  assign seq_hr_chan_reg3     = dr_sram[8'h46] & 16'h000F; //ignore reserved bits 
  assign seq_lr_chan_reg1     = dr_sram[8'h7A] & 16'h7FE1; //ignore reserved bits
  assign seq_lr_chan_reg2     = dr_sram[8'h7B];
  assign seq_lr_chan_reg3     = dr_sram[8'h7C] & 16'h000F; //ignore reserved bits
  assign seq_avg_reg1         = dr_sram[8'h4A] & 16'h4FE0; //ignore reserved bits
  assign seq_avg_reg2         = dr_sram[8'h4B];
  assign seq_avg_reg3         = dr_sram[8'h47] & 16'h000F; //ignore reserved bits
  assign seq_bipolar_reg1     = dr_sram[8'h4C] & 16'h0800; //ignore reserved bits
  assign seq_bipolar_reg2     = dr_sram[8'h4D];
  assign seq_acq_ext_reg1     = dr_sram[8'h4E] & 16'h0800; //ignore reserved bits
  assign seq_acq_ext_reg2     = dr_sram[8'h4F];
 
  assign seq_hr_chan_reg_comb = {seq_hr_chan_reg3, seq_hr_chan_reg2, seq_hr_chan_reg1};
  assign seq_lr_chan_reg_comb = {seq_lr_chan_reg3, seq_lr_chan_reg2, seq_lr_chan_reg1};
  assign seq_acq_ext_reg_comb = {16'h0000,seq_acq_ext_reg2,seq_acq_ext_reg1};
  assign seq_bipolar_reg_comb = {16'h0000,seq_bipolar_reg2,seq_bipolar_reg1};
  //

  assign op_mode            = cfg_reg1[15:12];
  assign default_mode       = (op_mode == 4'b0000 || op_mode[3:2] == 2'b11);
  assign single_pass_mode   = (op_mode == 4'b0001);
  assign cont_seq_mode      = (op_mode == 4'b0010);
  assign single_chan_mode   = (op_mode == 4'b0011);
  assign single_chan_id     = cfg_reg0[5:0];
  assign ext_mux_chan_id    = cfg_reg0[5:0];
  assign ext_mux_en         = cfg_reg0[11] && (~default_mode || single_chan_mode);
  assign ext_mux            = cfg_reg0[11];
  assign event_driven_mode  = cfg_reg0[9];
  assign cont_sampl_mode    = !event_driven_mode;
  assign bipolar_mode       = cfg_reg0[10];
  assign single_pass_active = single_pass_mode && ~(single_pass_finished && cont_sampl_mode);

  always @(posedge sysmon_rst or posedge DCLK_in) begin //at initialization or sequence restart
    if( sysmon_rst) begin 
      alm_en  <= 0;
      ot_en   <= 0;
    end
    else if(initialize[2] || single_pass_finished_pe || chan_asrt_5) begin
      if (default_mode) begin
        alm_en  <= 0;
        ot_en   <= 1;
      end
      else begin
        ot_en        <= ~cfg_reg1[0];
        alm_en[2:0]  <= ~cfg_reg1[3:1];
        alm_en[6:3]  <= ~cfg_reg1[11:8];
        alm_en[11:8] <= ~cfg_reg3[3:0]; 
      end
    end
  end

  //6V range support for VUSER0-3
  //0: 0-3V, 1: 0-6V
  assign bank_sel_6V[3:0] = cfg_reg4[3:0]; // CR 949547

  assign single_pass_finished_pe = single_pass_finished & ~single_pass_finished_d;

  always @(posedge DCLK_in or posedge sysmon_rst) begin
    if(sysmon_rst) begin
      single_pass_finished   <= 0;
      single_pass_finished_d <= 0;
    end
    else begin
      if(|initialize )begin
        single_pass_finished   <= 0;
        single_pass_finished_d <= 0;
      end
      else begin
        if(single_pass_mode &&
           ((!acq_ext_cur && EOS_out)||
            (acq_ext_cur && hr_final_conversion && adc_state==ST_A_WAIT && busy_start_cs)) )
          single_pass_finished   <= 1;
        single_pass_finished_d <= single_pass_finished;
      end   
    end
  end

  //-------------------------------------------------------------------------
  //---- I2C logic start   --------------------------------------------------
  //---- PMBus logic start --------------------------------------------------
  //-------------------------------------------------------------------------
   
  parameter  ST_I2C_IDLE      = 2'd0,
             ST_I2C_GET_ADDR  = 2'd1,
             ST_I2C_GET_CMD   = 2'd2,
             ST_I2C_READ      = 2'd3;

  localparam I2C_DRP_RD = 4'b0001; // read 
  localparam I2C_DRP_WR = 4'b0010; // write
  localparam I2C_DRP_NO = 4'b0000; // no operation
  
  parameter  ST_PMB_IDLE      = 3'd0,
             ST_PMB_GET_ADDR  = 3'd1,
             ST_PMB_GET_CMD   = 3'd2,
             ST_PMB_WRITE     = 3'd3,
             ST_PMB_READ      = 3'd4;


  localparam PMB_ALERT_RESPONSE_ADDR    = 7'b0001100;

   
  reg  [1:0]  i2c_state;
  reg         i2c_start;
  reg         i2c_start_reset;
  reg         i2c_stop;
  reg         i2c_stop_reset;
  reg  [3:0]  i2c_bit_counter;
  reg  [2:0]  i2c_byte_counter;
  wire        i2c_lsb_bit;
  wire        i2c_ack_bit;
  wire [3:0]  i2c_drp_cmd ;
  reg  [31:0] i2c_cmd_in;
  reg  [7:0]  i2c_data_in;
  wire        i2c_addr_match;
  wire        i2c_addr_match_wop;
  wire        i2c_rw_bit;
  wire        i2c_rd_cmd_pre;
  reg         i2c_rd_cmd;
  reg         i2c_ack_in; //ack from master to slave, negated.
  wire        i2c_cmd_end;
  wire        i2c_rd_end;
  reg         i2c_cmd_received;
  reg  [15:0] i2c_data_out;

  reg  [2:0]  pmb_state;
  reg  [2:0]  pmb_tot_bytes;
  wire        pmb_data_end;
  wire [7:0]  pmb_cmd_pre;
  reg  [31:0] pmb_data_out;
  reg         pmb_wr_exec_2;
  reg         pmb_wr_exec_d;
  wire        pmb_wr_exec_pe;
  reg [7:0]   pmb_curr_chan_id;
  reg         pmb_read_only_cmd;
  reg  [7:0]  pmb_status_vout;
  reg  [7:0]  pmb_status_temperature;
  reg  [7:0]  pmb_status_cml;
  reg  [7:0]  pmb_clr_status_vout;
  reg  [7:0]  pmb_clr_status_temperature;
  reg  [7:0]  pmb_clr_status_cml;
  reg  [7:0]  pmb_status_word; //upper byte
  reg  [7:0]  pmb_status_byte; //lower byte
  reg         pmb_unsp_cmd;
  reg         pmb_unsp_data;
  reg         pmb_paged;
  reg         pmb_selected;
  reg  [7:0]  pmb_page_index;
  reg  [7:0]  pmb_page_stat;
  reg  [7:0]  pmb_page_max;  //max stored value address
  reg  [7:0]  pmb_page_min;  //min stored value address
  reg  [7:0]  pmb_page_up_l; //upper limit register address
  reg  [7:0]  pmb_page_lo_l; //lower limit register address
  reg  [3:0]  pmb_page_alm_id; //alarm index for over/under voltage
  reg         pmb_page_6V;
  wire        pmb_ara_rcvd;
  reg         pmb_ara; //alert response address
  reg         clear_faults;
  wire        pmb_clear;
   
   
  //i2c or pmbus selection changes on the fly with i2c command address selection
  //i2c_addr_match_wop -> i2c address match without protocol match
  assign i2c_addr_match_wop = ((i2c_data_in[7:4]==i2c_device_addr[6:3]) && (i2c_data_in[2:1]==i2c_device_addr[1:0])) ? 1 : 0;
  assign i2c_addr_match     = ((i2c_oride && (i2c_data_in[7:1]==i2c_device_addr[6:0])) ||  
                               (~i2c_oride && i2c_addr_match_wop ))
                               ? 1 : 0;
  assign pmb_en_bit         = i2c_data_in[3] && i2c_ack_bit && (i2c_state==ST_I2C_GET_ADDR || pmb_state==ST_PMB_GET_ADDR); //0:i2c, 1:pmbus 

  assign pmb_ara_rcvd       = ((i2c_data_in[6:0]==PMB_ALERT_RESPONSE_ADDR || i2c_data_in[7:1]==PMB_ALERT_RESPONSE_ADDR ) && 
                               (i2c_lsb_bit ||i2c_ack_bit));

  assign pmb_clear          = pmb_ara || clear_faults;

  always @(posedge RESET_in or negedge I2C_SCLK_in or posedge i2c_stop) begin
    if (RESET_in || i2c_stop ) 
      pmb_ara <= 0; //this should be a pulse.
    else begin
      if (pmb_state==ST_PMB_IDLE) 
        pmb_ara <= 0; //this should be a pulse.
      else 
        pmb_ara <= pmb_ara_rcvd && (pmb_state==ST_PMB_GET_ADDR) && i2c_rd_cmd_pre; 
    end
  end
  
  assign pmb_en = !i2c_en;
  always @(posedge RESET_in or negedge I2C_SCLK_in) begin
    if (RESET_in) begin
      i2c_en <=1;
    end
    else begin
      if(i2c_oride)
        i2c_en <= ~cfg_reg3[10];
      else if(i2c_ack_bit && (i2c_state==ST_I2C_GET_ADDR || pmb_state==ST_PMB_GET_ADDR) && i2c_addr_match_wop)
        i2c_en <= ~i2c_data_in[3];
    end
  end

  always @(posedge RESET_in or posedge i2c_start_reset or negedge I2C_SDA_in) begin
    if(RESET_in || i2c_start_reset) 
      i2c_start <= 1'b0;
    else
      i2c_start <= I2C_SCLK_in;
  end

  always @(posedge RESET_in or posedge I2C_SCLK_in) begin
    if(RESET_in)
      i2c_start_reset <= 1'b0;
    else
      i2c_start_reset <= i2c_start;
  end
   
  always @(posedge RESET_in or posedge i2c_stop_reset or posedge I2C_SDA_in) begin
    if(RESET_in || i2c_stop_reset) 
      i2c_stop <= 1'b0;
    else
      i2c_stop <= I2C_SCLK_in;
  end

  always @(posedge RESET_in or posedge i2c_stop) begin
    if(RESET_in)
      i2c_stop_reset = 1'b0;
    else begin
      repeat (16) @(posedge DCLK_in);
      i2c_stop_reset = 1;
      repeat (16) @(posedge DCLK_in);
      i2c_stop_reset = 0;
    end
  end

  assign i2c_lsb_bit = (i2c_bit_counter== 4'd7) && ~i2c_start;
  assign i2c_ack_bit = (i2c_bit_counter== 4'd8) && ~i2c_start;

  always @(posedge RESET_in or negedge I2C_SCLK_in or posedge i2c_start) begin
    if(RESET_in || i2c_start)
      i2c_bit_counter <= 'd0;
    else begin
      if (i2c_ack_bit)
        i2c_bit_counter <= 'd0;
      else
        i2c_bit_counter <= i2c_bit_counter + 'd1;
      end
  end      

  always @(posedge RESET_in or posedge I2C_SCLK_in) begin
    if(RESET_in)
      i2c_data_in <= 'd0;
    else if(!i2c_ack_bit)
      i2c_data_in <= {i2c_data_in[6:0],I2C_SDA_in} ;
  end

  assign i2c_drp_data = i2c_cmd_in[15:0];
  assign i2c_drp_addr = i2c_cmd_in[25:16];
  assign i2c_drp_cmd  = i2c_cmd_in[29:26];


  always @(posedge I2C_SCLK_in) begin
    //if(RESET_in)
    //  i2c_cmd_in <= 'd0;
    //else if(i2c_ack_bit && i2c_state == ST_I2C_GET_CMD )
    if(i2c_ack_bit && i2c_state == ST_I2C_GET_CMD )
      i2c_cmd_in <= {i2c_data_in,i2c_cmd_in[31:8]} ;
  end

  assign pmb_cmd_pre  = i2c_data_in[7:0];

  always @(posedge I2C_SCLK_in) begin
    //if(RESET_in)
    //  pmb_cmd_in <= 'd0;
    //else if (i2c_ack_bit && pmb_state == ST_PMB_GET_CMD)
    if (i2c_ack_bit && pmb_state == ST_PMB_GET_CMD)
      pmb_cmd_in <= i2c_data_in;
  end

  assign i2c_rw_bit     = i2c_lsb_bit && (i2c_state == ST_I2C_GET_ADDR || pmb_state ==ST_PMB_GET_ADDR);
  assign i2c_rd_cmd_pre = i2c_rw_bit && I2C_SDA_in; 
   
  always @(posedge RESET_in or posedge i2c_stop or negedge I2C_SCLK_in) begin
    if(RESET_in || i2c_stop)
      i2c_rd_cmd <= 1'b0;
    else begin
      if (i2c_state==ST_I2C_IDLE && pmb_state==ST_PMB_IDLE)
        i2c_rd_cmd <= 1'b0;
      else if (i2c_rw_bit ) 
        i2c_rd_cmd <= i2c_data_in[0] ;
    end
  end

  always @(posedge RESET_in or posedge I2C_SCLK_in) begin
    if(RESET_in)
      i2c_ack_in <= 'd0;
    else if(i2c_ack_bit)
      i2c_ack_in <= ~I2C_SDA_in; //ACK from master to slave, negated.
    else if ((i2c_state==ST_I2C_IDLE && pmb_state==ST_PMB_IDLE) || i2c_bit_counter=='d1)
      i2c_ack_in <= 0;
  end

  assign i2c_cmd_end = i2c_ack_bit && (i2c_byte_counter==3'd3);
  assign i2c_rd_end  = i2c_ack_bit && (i2c_byte_counter==3'd1);

  always @(posedge RESET_in or posedge i2c_stop or posedge I2C_SCLK_in) begin
    if(RESET_in || i2c_stop)
      i2c_cmd_received <= 0;
    else if (i2c_cmd_end)
      i2c_cmd_received <= 1;
    else if (i2c_state==ST_I2C_READ)
      i2c_cmd_received <= 0;
  end

  always @(posedge RESET_in or posedge i2c_stop or negedge I2C_SCLK_in) begin
    if(RESET_in || i2c_start || i2c_stop)
      i2c_byte_counter <= 0;
    else if(i2c_ack_bit && (i2c_state == ST_I2C_GET_CMD || i2c_state == ST_I2C_READ ||
                            pmb_state == ST_PMB_WRITE   || pmb_state == ST_PMB_READ )) 
      i2c_byte_counter <= i2c_byte_counter + 1;
  end

  //I2C state machine.
  always @(posedge RESET_in or posedge i2c_stop or negedge I2C_SCLK_in) begin
    if(RESET_in || i2c_stop)// && ~i2c_en)
      i2c_state <=  ST_I2C_IDLE;
    else if(i2c_start)
      i2c_state <= ST_I2C_GET_ADDR;
    else if (i2c_ack_bit)
      case (i2c_state) 
        ST_I2C_GET_ADDR : begin 
                            if(!(i2c_addr_match && !pmb_en_bit)) begin
                              i2c_state <= ST_I2C_IDLE;
                              $display("Info: [Unisim %s-54] I2C command address h%0X not matching the device address h%0X @time %0t", 
                                MODULE_NAME, i2c_data_in[7:1], i2c_device_addr, $time);
                            end
                            else if (~i2c_cmd_received)
                              i2c_state <= ST_I2C_GET_CMD;
                            else if(i2c_drp_cmd==I2C_DRP_RD) //if you received a command earlier, it had to be a drp read command.
                              i2c_state <= ST_I2C_READ;
                            else
                              i2c_state <= ST_I2C_IDLE;
                          end
        ST_I2C_GET_CMD  : begin
                            if (i2c_cmd_end) begin
                              i2c_state <= ST_I2C_IDLE;
                              $display("Info: [Unisim %s] I2C command received @time %0t", MODULE_NAME, $time);
                            end
                          end
        ST_I2C_READ     : begin
                            if(i2c_rd_end)
                              i2c_state <= ST_I2C_IDLE;
                          end
        default         : i2c_state <= ST_I2C_IDLE;
      endcase
      end      

  //i2c write command execute    
  assign i2c_wr_exec = (i2c_cmd_received && i2c_drp_cmd==I2C_DRP_WR);

  always @(posedge DCLK_in ) begin
    if(!sysmon_rst) begin
      if(i2c_wr_exec &&
         !(is_readonly_address(i2c_drp_addr)) && !is_reserved_address(i2c_drp_addr) )
          dr_sram[i2c_drp_addr] <= i2c_drp_data;
    end
  end
  
  //i2c read command execute   
  always @(negedge I2C_SCLK_in) begin
    if(!RESET_in) begin
      if(i2c_cmd_received && i2c_drp_cmd==I2C_DRP_RD && i2c_state==ST_I2C_GET_ADDR && !i2c_ack_bit) begin //fetch the data
        if(i2c_drp_addr>='h40)
          i2c_data_out <= dr_sram[i2c_drp_addr];
        else
          i2c_data_out <= data_reg[i2c_drp_addr];
      end
      else if(i2c_lsb_bit && i2c_state==ST_I2C_READ)
        i2c_data_out <= {8'b0,i2c_data_out[15:8]};// shift the higher byte to lower.
      else //shift the data 1 bit at a time for only the lower byte. bit 7 is pushed out.
        i2c_data_out <= {i2c_data_out[15:8],i2c_data_out[6:0],1'b0}; 
    end
  end
   
  assign pmb_data_end = i2c_ack_bit && (i2c_byte_counter==(pmb_tot_bytes-1));

  //Pull down SDA to transfer a zero to the master.
  always@(posedge RESET_in or negedge I2C_SCLK_in) begin
    if (RESET_in)
      I2C_SDA_TS_out <= 1;
    else begin
      if (i2c_start)
        I2C_SDA_TS_out <= 1;
      else if (i2c_lsb_bit) //acknowledge the end of a 1 byte transfer from master
        I2C_SDA_TS_out <= ! (((i2c_state==ST_I2C_GET_ADDR) && (i2c_addr_match || pmb_ara_rcvd)) || //will also be true for pmbus
                             ((i2c_state==ST_I2C_GET_CMD ) && !(i2c_rd_cmd && i2c_byte_counter=='d3)) || //send NACK at the last byte of command, only if read command
                             (pmb_state==ST_PMB_GET_CMD) ||
                             (pmb_state==ST_PMB_WRITE)  //send ACK for all write command bytes
                            );
      else if ((i2c_ack_bit && //first bit of next slave to master transfer
               ((i2c_state==ST_I2C_GET_ADDR) && (i2c_drp_cmd==I2C_DRP_RD) )) || 
               (i2c_state==ST_I2C_READ && !i2c_rd_end)) //or read continued
        I2C_SDA_TS_out <= i2c_data_out[7];
      else if(((i2c_ack_bit && pmb_state==ST_PMB_GET_ADDR) && i2c_rd_cmd) || //first bit of next slave to master transfer
                (pmb_state==ST_PMB_READ && !pmb_data_end)) //or read continued
        I2C_SDA_TS_out <= pmb_data_out[7];
      else
        I2C_SDA_TS_out <= 1;
    end
  end

  // clock stretching      
  assign I2C_SCLK_TS_out = 1'b1;
   
  //---- End of I2C logic ------------------------------------------------
  //---- PMBUS only from here on -----------------------------------------
      
  // PMBUS state machine 
  always @(posedge RESET_in or posedge i2c_stop or negedge I2C_SCLK_in) begin
    if(RESET_in || i2c_stop)
      pmb_state <=  ST_PMB_IDLE;
    else if(i2c_start)
      pmb_state <= ST_PMB_GET_ADDR;
    else if (i2c_ack_bit)
      case (pmb_state) 
        ST_PMB_GET_ADDR : begin 
                            if(!(i2c_addr_match && pmb_en_bit)) begin
                              if(pmb_ara_rcvd) begin
                                if(!i2c_rd_cmd) begin
                                  pmb_state <= ST_PMB_IDLE;
                                  $display("Info: [Unisim %s-57] PMBus Alert Response Address received together with a write bit instead of a read bit. It will be ignored. @time %0t", 
                                    MODULE_NAME, $time);
                                end
                                else //ARA received. Send the device address as a response
                                  pmb_state <= ST_PMB_READ;
                              end
                              else begin
                                pmb_state <= ST_PMB_IDLE;
                                if(pmb_en_bit)
                                  $display("Info: [Unisim %s-64] PMBus command address h%0X not matching the device address h%0X @time %0t", 
                                    MODULE_NAME, i2c_data_in[7:1], i2c_device_addr, $time);
                              end
                            end
                            else if (!i2c_rd_cmd) //write command comes only before command id.
                              pmb_state <= ST_PMB_GET_CMD;
                            else 
                              pmb_state <= ST_PMB_READ;
                          end
        ST_PMB_GET_CMD  : begin
                            $display("Info: [Unisim %s] PMBus command received @time %0t", MODULE_NAME, $time);
                            if(pmb_cmd_pre==CMD_CLEAR_FAULT) //clear fault has 0 bytes of succeeding data, so go to idle.
                              pmb_state <= ST_PMB_IDLE;
                            else //get succeeding data. if it is a read command, restart will take it to ST_PMB_IDLE.
                              pmb_state <= ST_PMB_WRITE;
                          end
        ST_PMB_WRITE    : begin
                            if(pmb_data_end)
                              pmb_state <= ST_PMB_IDLE;
                          end
        ST_PMB_READ     : begin
                            if(pmb_data_end)
                              pmb_state <= ST_PMB_IDLE;
                          end
        default         : begin
                            pmb_state <= ST_PMB_IDLE;
                          end
      endcase
  end
   

  //Parse PMB command
  always @(posedge RESET_in or negedge I2C_SCLK_in) begin
      if(RESET_in) begin
      pmb_tot_bytes <= 'd0;
      pmb_unsp_cmd  <= 0;
      pmb_paged     <= 0;
      pmb_selected  <= 0;
      end
    else if(i2c_ack_bit && pmb_state==ST_PMB_GET_CMD) begin
      pmb_unsp_cmd <= 0;
      case (pmb_cmd_pre)
        CMD_PAGE                : begin 
                                    pmb_tot_bytes <= 'd1;
                                    pmb_paged     <= 1;
                                  end    
        CMD_CLEAR_FAULT         : begin 
                                    pmb_tot_bytes <= 'd0;
                                  end    
        CMD_CAPABILITY,CMD_VOUT_MODE,CMD_STATUS_BYTE, 
        CMD_STATUS_VOUT,  CMD_STATUS_TEMPERATURE, CMD_STATUS_CML,
        CMD_PMBUS_REVISION,  CMD_MFR_ENABLE_VUSER_HR
                                : begin 
                                    pmb_tot_bytes <= 'd1;
                                  end                      
        CMD_VOUT_OV_FAULT_LIMIT, CMD_VOUT_UV_FAULT_LIMIT,
        CMD_OT_FAULT_LIMIT     , CMD_OT_WARNING_LIMIT   ,
        CMD_UT_WARNING_LIMIT   , CMD_UT_FAULT_LIMIT     ,
        CMD_STATUS_WORD        , CMD_READ_VOUT          ,
        CMD_READ_TEMPERATURE_1 , CMD_MFR_ACCESS_REG     , 
        CMD_MFR_READ_VOUT_MAX  , CMD_MFR_READ_VOUT_MIN  , 
        CMD_MFR_READ_TEMP_MAX  , CMD_MFR_READ_TEMP_MIN    
                                : begin 
                                    pmb_tot_bytes <= 'd2;
                                  end   
        CMD_MFR_ID,CMD_MFR_MODEL: begin 
                                    pmb_tot_bytes <= 'd4;
                                  end
        CMD_MFR_REVISION        : begin 
                                    pmb_tot_bytes <= 'd3;
                                  end  
        CMD_MFR_SELECT_REG      : begin 
                                    pmb_tot_bytes <= 'd2;
                                    pmb_selected  <= 1;
                                  end
        default:                  begin
                                    pmb_unsp_cmd<=1; //Unsupported command
                                    $display("Warning: [Unisim %s-56] PMBus received invalid command ID h%0X @ time %0t ", MODULE_NAME, pmb_cmd_pre, $time);
                                  end      
      endcase

    end
    else if(pmb_ara_rcvd && pmb_state==ST_PMB_GET_ADDR) //Alert Response Address (ARA) has 1 byte response.
      pmb_tot_bytes <= 1;
    else begin
      pmb_unsp_cmd  <= 0;
    end
  end
 
  always @(posedge RESET_in or posedge i2c_stop or negedge I2C_SCLK_in) begin
    if(RESET_in ||i2c_stop) 
      clear_faults  <= 0;
    else if(i2c_ack_bit && pmb_state==ST_PMB_GET_CMD && pmb_cmd_pre==CMD_CLEAR_FAULT)
      clear_faults  <= 1;
    else
      clear_faults  <= 0;
  end

  always @(posedge RESET_in or posedge I2C_SCLK_in) begin
    if (RESET_in)
      pmb_data_in <= 'd0;
    else if(i2c_ack_bit && pmb_state == ST_PMB_WRITE)
      if(pmb_tot_bytes>1)
        pmb_data_in <= {i2c_data_in,pmb_data_in[15:8]} ; //Most significant byte arrives later.
      else
        pmb_data_in <= {8'd0,i2c_data_in} ; //1 byte, that's it.
  end

  //convert from linear 16 to drp format -> PMBus WRITE
  function [15:0] linear16_to_drp;
    input [15:0] mantissa; //unsigned
    reg    [16:0] linear17_to_drp;
    begin
      if(pmb_page_6V) // CR 949547
        linear16_to_drp = (mantissa *2)/3;
      else begin
        linear17_to_drp = (mantissa *4)/3;
        if(linear17_to_drp > 17'h0FFFF) begin
          linear16_to_drp = 16'hFFFF; 
          if(pmb_wr_exec_pe) //display message only once.
            $display("Warning: [Unisim %s-62] The maximum value you can write to a DRP supply register is 16'hFFFF. Hence for PMBus it is 16'hAAAA. The input value has been saturated to max.", MODULE_NAME, $time);
        end
        else 
          linear16_to_drp = linear17_to_drp[15:0];
      end
      //$display("linear16_to_drp: mantissa :h%0h, output=h%0h @%0t",mantissa , linear16_to_drp, $time);
    end
  endfunction

  //convert from drp format to linear 16 -> PMBus READ
  function [15:0]  drp_to_linear16;
    input  [15:0] voltage_drp; //unsigned
    reg    [16:0] drp_to_linear17;
    begin
      if(pmb_page_6V) begin // CR 949547
        drp_to_linear17 = (voltage_drp *3)/2;
        if(drp_to_linear17 > 17'h0FFFF) begin
          drp_to_linear16 = 16'hFFFF; 
          if(i2c_lsb_bit) //display message only once
            $display("Warning: [Unisim %s-63] The maximum value you can read from a DRP supply register is 16'hFFFF. Hence for PMBus it is 16'hAAAA. The return value has been saturated to max.", MODULE_NAME, $time);
        end
        else
          drp_to_linear16 = drp_to_linear17[15:0];
      end
      else
      drp_to_linear16 = (voltage_drp *3)/4;
      //$display("drp_to_linear16: voltage_drp=h%0h, output=h%0h, drp_to_linear17=h%0h @%0t",voltage_drp, drp_to_linear16, drp_to_linear17, $time);
    end
  endfunction

  //convert from linear 11 to integer -> PMBus WRITE
  function [15:0] linear11_to_drp;
    input [15:0] exp_mants; //both signed
    //input        limit; // 0 if reading current or min/max value 1: reading temp limits 
    real exp;
    real mants;
    real temp_coeff;
    real temp_offset;
    real two_p_bits;
    real real_result;
    begin
      exp         =$signed(exp_mants[15:11]);
      mants       =$signed(exp_mants[10:0]);
      //temp_coeff  = limit ? 502.9098 : 491.2065 ;
      //temp_offset = limit ? 273.8195  : 273.15 ;
      //two_p_bits  = limit ? 65536: 65535;
      temp_coeff   = 503.975 ;
      temp_offset = 273.15 ;
      two_p_bits  = 65536;
      real_result = (mants * (2** exp)); //mants * 2^exp
      real_result = (real_result + temp_offset) * (two_p_bits / temp_coeff);
      //linear11_to_drp = $rtoi(real_result);
      linear11_to_drp = real_result;
      //$display("linear11_to_drp: exp_mants=h%0h, mantissa=d%0d, exp:d%0d, real_result=g%0g, output=h%0h @%0t\n",
      //  exp_mants, mants, exp, real_result, linear11_to_drp, $time/1000);
    end    
  endfunction

  // Convert from integer to to linear 11 -> PMBus READ
  // Exponent is -1 hard coded during PMBus reads.
  function [15:0] drp_to_linear11;
    input  [15:0] drp_temp; //unsigned. temperature in drp format
    //input         limit;
    real          temp_coeff;
    real          temp_offset;
    real          two_p_bits;
    real          real_result;
    reg signed [10:0] mantissa;   
    begin
      //temp_coeff  = limit ? 502.9098 : 491.2065 ;
      //temp_offset = limit ? 273.8195  : 273.15 ;
      //two_p_bits  = limit ? 65536: 65535;
      temp_coeff      = 503.975;
      temp_offset     = 273.15;
      two_p_bits      = 65536;
      real_result     = 2* ((drp_temp * temp_coeff / two_p_bits) - temp_offset);
      //mantissa        = $rtoi (real_result); 
      mantissa        = real_result; 
      drp_to_linear11 = {5'h1F,mantissa}; 
      //$display("drp_to_linear11: drp_temp=h%0h, real_result = g%0g, real_result = h%0g, mantissa=h%0h, output= h%0h @%0t\n",
      // drp_temp, real_result, real_result, mantissa, drp_to_linear11, $time/1000);
    end
  endfunction

  always @(posedge RESET_in or posedge i2c_stop or posedge i2c_start or negedge I2C_SCLK_in) begin
    if(RESET_in ||i2c_stop ||i2c_start )
      pmb_wr_exec <= 0;
    else if (pmb_state==ST_PMB_WRITE && pmb_data_end)
      pmb_wr_exec <= 1;
    else
      pmb_wr_exec <= 0;
  end

  assign pmb_wr_exec_pe = pmb_wr_exec & ~pmb_wr_exec_d;

  always @(posedge RESET_in or posedge i2c_stop or posedge i2c_start or posedge DCLK_in) begin
    if(RESET_in ||i2c_stop ||i2c_start )
      pmb_wr_exec_d <= 0;
    else 
      pmb_wr_exec_d <= pmb_wr_exec;
  end
      
  always @(posedge DCLK_in) begin
    @(posedge pmb_wr_exec);
    if (pmb_cmd_in==CMD_PAGE ||
        pmb_cmd_in==CMD_VOUT_UV_FAULT_LIMIT ||
        pmb_cmd_in==CMD_VOUT_OV_FAULT_LIMIT ||
        pmb_cmd_in==CMD_OT_FAULT_LIMIT ||
        pmb_cmd_in==CMD_OT_WARNING_LIMIT ||
        pmb_cmd_in==CMD_UT_FAULT_LIMIT ||
        pmb_cmd_in==CMD_UT_WARNING_LIMIT ||
        pmb_cmd_in==CMD_MFR_ACCESS_REG
       )
    @(negedge pmb_wr_exec);
    @(posedge DCLK_in);
    pmb_wr_exec_2 = 1;
    @(posedge DCLK_in);
    pmb_wr_exec_2 = 0;
  end

  //PMB write execute 
  always @(posedge RESET_in or posedge pmb_wr_exec or posedge DCLK_in) begin
    if(RESET_in) begin
      pmb_read_only_cmd          <=0;
      pmb_clr_status_vout        <='d0;
      pmb_clr_status_temperature <='d0;
      pmb_clr_status_cml         <='d0;
      pmb_drsram_wr_data         <='d0;
      pmb_drsram_addr            <='d0;
    end
    else if(pmb_wr_exec) begin
      pmb_read_only_cmd          <=0;
      pmb_clr_status_vout        <='d0;
      pmb_clr_status_temperature <='d0;
      pmb_clr_status_cml         <='d0;
      pmb_drsram_wr_data         <='d0;
      pmb_drsram_addr            <='d0;
      case (pmb_cmd_in)
        CMD_PAGE                : ; //seperated to another always block for readibility
        CMD_CLEAR_FAULT         : pmb_read_only_cmd          <=1; //Error: Too many bytes
        CMD_VOUT_OV_FAULT_LIMIT : begin
                                    dr_sram[pmb_page_up_l]     <= linear16_to_drp(pmb_data_in[15:0]); 
                                    pmb_drsram_wr_data         <= linear16_to_drp(pmb_data_in[15:0]);
                                    pmb_drsram_addr            <= pmb_page_up_l;
                                  end
        CMD_VOUT_UV_FAULT_LIMIT : begin
                                    dr_sram[pmb_page_lo_l]     <= linear16_to_drp(pmb_data_in[15:0]);
                                    pmb_drsram_wr_data         <= linear16_to_drp(pmb_data_in[15:0]);
                                    pmb_drsram_addr            <= pmb_page_lo_l;
                                  end
        CMD_OT_FAULT_LIMIT      : begin
                                    dr_sram[8'h53]             <= linear11_to_drp(pmb_data_in[15:0]); 
                                    pmb_drsram_wr_data         <= linear11_to_drp(pmb_data_in[15:0]);
                                    pmb_drsram_addr            <= 8'h53;
                                  end
        CMD_OT_WARNING_LIMIT    : begin
                                    dr_sram[8'h50]             <= linear11_to_drp(pmb_data_in[15:0]); 
                                    pmb_drsram_wr_data         <= linear11_to_drp(pmb_data_in[15:0]);
                                    pmb_drsram_addr            <= 8'h50;
                                  end
        CMD_UT_WARNING_LIMIT    : begin
                                    dr_sram[8'h54]             <= linear11_to_drp(pmb_data_in[15:0]); 
                                    pmb_drsram_wr_data         <= linear11_to_drp(pmb_data_in[15:0]);
                                    pmb_drsram_addr            <= 8'h54;
                                  end
        CMD_UT_FAULT_LIMIT      : begin
                                    dr_sram[8'h57]             <= linear11_to_drp(pmb_data_in[15:0]); 
                                    pmb_drsram_wr_data         <= linear11_to_drp(pmb_data_in[15:0]);
                                    pmb_drsram_addr            <= 8'h57;
                                  end
        CMD_STATUS_VOUT         : pmb_clr_status_vout        <= pmb_data_in[7:0];
        CMD_STATUS_TEMPERATURE  : pmb_clr_status_temperature <= pmb_data_in[7:0];
        CMD_STATUS_CML          : pmb_clr_status_cml         <= pmb_data_in[7:0];
        CMD_MFR_SELECT_REG      : begin
                                    pmb_sel_addr             <= pmb_data_in[7:0];
                                    // Checked reserved error message
                                    if(is_reserved_address(pmb_sel_addr))
                                      $display("Warning: [Unisim %s] PMBus MFR_SELECT_REG command is trying to point to a RESERVED location h%0X.", MODULE_NAME, pmb_sel_addr, $time/1000.0);
                                  end
        CMD_MFR_ACCESS_REG      : begin
                                    if(pmb_sel_addr >= 8'h40)
                                      dr_sram[pmb_sel_addr]  <= pmb_data_in[15:0];
                                    pmb_drsram_addr    <= pmb_sel_addr; 
                                    pmb_drsram_wr_data <= pmb_data_in[15:0]; 
                                  end              
        CMD_CAPABILITY         , CMD_VOUT_MODE         ,
        CMD_STATUS_BYTE        , CMD_STATUS_WORD       ,
        CMD_READ_VOUT          , CMD_READ_TEMPERATURE_1,
        CMD_PMBUS_REVISION     , CMD_MFR_ID            ,
        CMD_MFR_MODEL          , CMD_MFR_REVISION      ,
        CMD_MFR_READ_VOUT_MAX  , CMD_MFR_READ_VOUT_MIN ,
        CMD_MFR_READ_TEMP_MAX  , CMD_MFR_READ_TEMP_MIN ,
        CMD_MFR_ENABLE_VUSER_HR: 
                                  begin 
                                    pmb_read_only_cmd        <=1; //Error: Too many bytes
                                  end
        //default:                  
        endcase    
    end //else if
    else begin //pmb_wr_exec==0 and posedge (dclk_in)
      pmb_read_only_cmd          <=0;
      pmb_clr_status_vout        <='d0;
      pmb_clr_status_temperature <='d0;
      pmb_clr_status_cml         <='d0;
      // Keep pmb_drsram_addr and pmb_drsram_wr_data values 
      // as they will be used with delay
    end
  end //always

  //PMB write execute for page command
  always @(posedge RESET_in or posedge pmb_wr_exec or negedge I2C_SCLK_in) begin
    if(RESET_in) begin
      pmb_drsram_bit_idx   <= 'd0;
      pmb_drsram_addr_page <= 'd0;
      pmb_page_index       <= 'd0;
      pmb_page_stat        <= 'd0;
      pmb_page_max         <= 'd0;
      pmb_page_min         <= 'd0;
      pmb_page_up_l        <= 'd0;
      pmb_page_lo_l        <= 'd0;
      pmb_page_alm_id      <= 'd1;
      pmb_valid_page       <= 0;
      pmb_page_6V          <= 0;
    end
    else if(pmb_wr_exec && pmb_cmd_in==CMD_PAGE) begin // || pmb_cmd_in==CMD_MFR_SELECT_REG) begin
      pmb_page_index    <= pmb_data_in[7:0];
      pmb_drsram_bit_idx  <= 'd0;
      pmb_drsram_addr_page<= 'd0;
      case (pmb_data_in[7:0]) 
        8'd1: begin //VCC INT
                dr_sram[8'h48][9]<= 1'b1; //Add this channel to sequence
                pmb_drsram_addr_page <= 8'h48;
                pmb_drsram_bit_idx   <= 'd9;
                pmb_page_stat     <= 8'h01;
                pmb_page_max      <= 8'h21;
                pmb_page_min      <= 8'h25;
                pmb_page_up_l     <= 8'h51;
                pmb_page_lo_l     <= 8'h55;
                pmb_page_alm_id   <= 'd1;
                pmb_valid_page       <= 1;
                pmb_page_6V       <= 0;
              end
        8'd2: begin //VCC AUX
                dr_sram[8'h48][10]<= 1'b1;
                pmb_drsram_addr_page <= 8'h48;
                pmb_drsram_bit_idx   <= 'd10;
                pmb_page_stat     <= 8'h02;
                pmb_page_max      <= 8'h22;
                pmb_page_min      <= 8'h26;
                pmb_page_up_l     <= 8'h52;
                pmb_page_lo_l     <= 8'h56;
                pmb_page_alm_id   <= 'd2;
                pmb_valid_page       <= 1;
                pmb_page_6V       <= 0;
               end
        8'd6: begin //VCC BRAM
                dr_sram[8'h48][14]<= 1'b1;
                pmb_drsram_addr_page <= 8'h48;
                pmb_drsram_bit_idx   <= 'd14;
                pmb_page_stat     <= 8'h06;
                pmb_page_max      <= 8'h23;
                pmb_page_min      <= 8'h27;
                pmb_page_up_l     <= 8'h58;
                pmb_page_lo_l     <= 8'h5C;
                pmb_page_alm_id   <= 'd3;
                pmb_valid_page       <= 1;
                pmb_page_6V       <= 0;
              end
        8'd13:begin // VCC PSINTLP
                dr_sram[8'h48][7]<= 1'b1;
                pmb_drsram_addr_page<= 8'h48;
                pmb_drsram_bit_idx  <= 'd7;
                pmb_page_stat    <= 8'h0D;
                pmb_page_max     <= 8'h28;
                pmb_page_min     <= 8'h2C;
                pmb_page_up_l    <= 8'h59;
                pmb_page_lo_l    <= 8'h5D;
                pmb_page_alm_id  <= 'd4;
                pmb_valid_page      <= 1;
                pmb_page_6V      <= 0;
              end
        8'd14:begin // VCC PSINTFP
                dr_sram[8'h48][6]<= 1'b1;
                pmb_drsram_addr_page<= 8'h48;
                pmb_drsram_bit_idx  <= 'd6;
                pmb_page_stat    <= 8'h0E;
                pmb_page_max     <= 8'h29;
                pmb_page_min     <= 8'h2D;
                pmb_page_up_l    <= 8'h5A;
                pmb_page_lo_l    <= 8'h5E;
                pmb_page_alm_id  <= 'd5;
                pmb_valid_page      <= 1;
                pmb_page_6V      <= 0;
              end
        8'd15:begin // VCC PSAUX
                dr_sram[8'h48][5]<= 1'b1;
                pmb_drsram_addr_page<= 8'h48;
                pmb_drsram_bit_idx  <= 'd5;
                pmb_page_stat    <= 8'h0F;
                pmb_page_max     <= 8'h2A;
                pmb_page_min     <= 8'h2E;
                pmb_page_up_l    <= 8'h5B;
                pmb_page_lo_l    <= 8'h5F;
                pmb_page_alm_id  <= 'd6;
                pmb_valid_page      <= 1;
                pmb_page_6V         <= 0;
              end
        8'd32:begin //VUSER 0
                dr_sram[8'h46][0]<= 1'b1;
                pmb_drsram_addr_page<= 8'h46;
                pmb_drsram_bit_idx  <= 'd0;
                pmb_page_stat    <= 8'h80;
                pmb_page_max     <= 8'hA0;
                pmb_page_min     <= 8'hA8;
                pmb_page_up_l    <= 8'h60;
                pmb_page_lo_l    <= 8'h68;
                pmb_page_alm_id  <= 'd8;
                pmb_valid_page      <= 1;
                pmb_page_6V         <= bank_sel_6V[0];
              end
        8'd33:begin //VUSER 1
                dr_sram[8'h46][1]<= 1'b1;
                pmb_drsram_addr_page<= 8'h46;
                pmb_drsram_bit_idx  <= 'd1;
                pmb_page_stat    <= 8'h81;
                pmb_page_max     <= 8'hA1;
                pmb_page_min     <= 8'hA9;
                pmb_page_up_l    <= 8'h61;
                pmb_page_lo_l    <= 8'h69;
                pmb_page_alm_id  <= 'd9;
                pmb_valid_page      <= 1;
                pmb_page_6V         <= bank_sel_6V[1];
              end
        8'd34:begin //VUSER 2
                dr_sram[8'h46][2]<= 1'b1;
                pmb_drsram_addr_page<= 8'h46;
                pmb_drsram_bit_idx  <= 'd2;
                pmb_page_stat    <= 8'h82;
                pmb_page_max     <= 8'hA2;
                pmb_page_min     <= 8'hAA;
                pmb_page_up_l    <= 8'h62;
                pmb_page_lo_l    <= 8'h6A;
                pmb_page_alm_id  <= 'd10;
                pmb_valid_page      <= 1;
                pmb_page_6V      <= bank_sel_6V[2];
              end 
        8'd35:begin //VUSER 3
                dr_sram[8'h46][3]<= 1'b1;
                pmb_drsram_addr_page<= 8'h46;
                pmb_drsram_bit_idx  <= 'd3;
                pmb_page_stat    <= 8'h83;
                pmb_page_max     <= 8'hA3;
                pmb_page_min     <= 8'hAB;
                pmb_page_up_l    <= 8'h63;
                pmb_page_lo_l    <= 8'h6B;
                pmb_page_alm_id  <= 'd11;
                pmb_valid_page      <= 1;
                pmb_page_6V      <= bank_sel_6V[3];
              end
        default:begin
                pmb_drsram_addr_page<= 'd0;
                pmb_drsram_bit_idx  <= 'd0;
                pmb_page_stat <= 8'd0;
                pmb_page_max  <= 8'd0;
                pmb_page_min  <= 8'd0;
                pmb_page_up_l <= 8'd0;
                pmb_page_lo_l <= 8'd0;
                pmb_page_alm_id  <= 'd1;
                pmb_valid_page      <= 0;
                pmb_page_6V         <= 0;
                $display("Warning: [Unisim %s-55] PMBus page command received an invalid Page index @ time %0t", MODULE_NAME, $time);
              end    
      endcase
    end // pmb_wr_exec
    else begin
    end        
  end //always

  //PMBus read execute
  always @(posedge RESET_in or negedge I2C_SCLK_in) begin
    if(RESET_in) 
      pmb_unsp_data <= 0; //unsupported data // This is not a read command
    else begin
      // need to fetch before we know if we are going to get a read or write request
      if(pmb_state==ST_PMB_GET_ADDR & !i2c_ack_bit) begin 
        pmb_data_out <= 32'h00000000;
        case (pmb_cmd_in)
          CMD_PAGE                : pmb_data_out[7:0]      <= pmb_page_index;
          CMD_CLEAR_FAULT         : begin 
                                      pmb_unsp_data        <= 1; //unsupported data // This is not a read command. validate after
                                      pmb_data_out[31:0]   <= 31'hXXXXXXXX;   //invalid command gets and x. 
                                    end
          CMD_CAPABILITY          : pmb_data_out[7:0]      <= 8'h30;
          CMD_VOUT_MODE           : pmb_data_out[7:0]      <= 8'h12;                 
          CMD_VOUT_OV_FAULT_LIMIT : pmb_data_out[15:0]     <= drp_to_linear16(dr_sram[pmb_page_up_l]);                                     
          CMD_VOUT_UV_FAULT_LIMIT : pmb_data_out[15:0]     <= drp_to_linear16(dr_sram[pmb_page_lo_l]);
          CMD_OT_FAULT_LIMIT      : pmb_data_out[15:0]     <= drp_to_linear11(dr_sram[8'h53]);
          CMD_OT_WARNING_LIMIT    : pmb_data_out[15:0]     <= drp_to_linear11(dr_sram[8'h50]);
          CMD_UT_WARNING_LIMIT    : pmb_data_out[15:0]     <= drp_to_linear11(dr_sram[8'h54]);
          CMD_UT_FAULT_LIMIT      : pmb_data_out[15:0]     <= drp_to_linear11(dr_sram[8'h57]);
          CMD_STATUS_BYTE         : pmb_data_out[7:0]      <= pmb_status_byte;
          CMD_STATUS_WORD         : pmb_data_out[15:0]     <= {pmb_status_word,pmb_status_byte};
          CMD_STATUS_VOUT         : pmb_data_out[7:0]      <= pmb_status_vout;
          CMD_STATUS_TEMPERATURE  : pmb_data_out[7:0]      <= pmb_status_temperature;
          CMD_STATUS_CML          : pmb_data_out[7:0]      <= pmb_status_cml;
          CMD_READ_VOUT           : begin 
                                      if(pmb_page_stat >= 8'h40)
                                        pmb_data_out[15:0] <= drp_to_linear16(dr_sram [pmb_page_stat]); 
                                      else
                                        pmb_data_out[15:0] <= drp_to_linear16(data_reg[pmb_page_stat]); 
                                    end  
          CMD_READ_TEMPERATURE_1  : pmb_data_out[15:0]      <= drp_to_linear11(data_reg[8'h00]); 
          CMD_PMBUS_REVISION      : pmb_data_out[7:0]      <= 8'h42;                 
          CMD_MFR_ID              : begin 
                                      pmb_data_out[7:0]    <= 8'h03; //in block read, first byte is the length of the rest of the data
                                      pmb_data_out[15:8]   <= 8'h93;                 
                                      pmb_data_out[23:16]  <= 8'h00;                 
                                      pmb_data_out[31:24]  <= 8'h00;                 
      
                                    end
          CMD_MFR_MODEL           : begin 
                                      pmb_data_out[7:0]    <= 8'h03; //in block read, first byte is the length of the rest of the data
                                      pmb_data_out[15:8]   <= 8'h00;                 
                                      pmb_data_out[23:16]  <= 8'h00;                 
                                      pmb_data_out[31:24]  <= 8'h00;                 
                                    end
          CMD_MFR_REVISION        : begin 
                                      pmb_data_out[7:0]    <= 8'h02; //in block read, first byte is the length of the rest of the data
                                      pmb_data_out[15:8]   <= 8'h00;                 
                                      pmb_data_out[23:16]  <= 8'h00;                 
                                    end
          CMD_MFR_SELECT_REG      : pmb_data_out[7:0]      <= pmb_sel_addr;
          CMD_MFR_ACCESS_REG      : begin 
                                      if(pmb_sel_addr >= 8'h40)
                                        pmb_data_out[15:0] <= dr_sram [pmb_sel_addr]; 
                                      else
                                        pmb_data_out[15:0] <= data_reg[pmb_sel_addr]; 
                                    end
          CMD_MFR_READ_VOUT_MAX   : begin 
                                      if(pmb_page_max>='h40)
                                        pmb_data_out[15:0] <= drp_to_linear16(dr_sram [pmb_page_max]);
                                      else
                                        pmb_data_out[15:0] <= drp_to_linear16(data_reg[pmb_page_max]);
                                    end
          CMD_MFR_READ_VOUT_MIN   : begin 
                                      if(pmb_page_min>='h40)
                                        pmb_data_out[15:0] <= drp_to_linear16(dr_sram [pmb_page_min]);
                                      else
                                        pmb_data_out[15:0] <= drp_to_linear16(data_reg[pmb_page_min]);
                                    end
          CMD_MFR_ENABLE_VUSER_HR : pmb_data_out[3:0]  <= cfg_reg4[3:0];   // as is
          CMD_MFR_READ_TEMP_MAX   : pmb_data_out[15:0] <= drp_to_linear11(data_reg[8'h20]); 
          CMD_MFR_READ_TEMP_MIN   : pmb_data_out[15:0] <= drp_to_linear11(data_reg[8'h24]); 
          default:                  begin
                                      pmb_data_out[31:0] <= 32'h00000000;   //invalid command
                                    end
        endcase

        if (pmb_ara_rcvd ) begin //&& (pmb_state==ST_PMB_GET_ADDR)) begin
          pmb_data_out[31:8] <= 24'd0;
          pmb_data_out[7:1]  <= i2c_device_addr | 7'b0000100;
          pmb_data_out[0]    <= 1'b0; //lsb of the response is don't care.
        end
      end
      else if (i2c_lsb_bit && pmb_state==ST_PMB_READ )
        pmb_data_out <= {8'b0,pmb_data_out[31:8]}; //shift the higher byte to lower
      else //shift the data 1 bit at a time for only the lower byte. bit 7 is pushed out.
        pmb_data_out <= {pmb_data_out[31:8],pmb_data_out[6:0],1'b0};
    end
  end //always

  // PMBus fault handling
  always @(posedge sysmon_rst or posedge pmb_clear or posedge DCLK_in) begin
    if(sysmon_rst || pmb_clear) begin
      pmb_status_word <= 'd0;
      pmb_status_byte <= 'd0;
    end
    else begin
      pmb_status_word[7]   <= |pmb_status_vout[7:0];
      pmb_status_word[6:0] <= 7'd0; //Reserved

      pmb_status_byte[7:6] <= 2'd0; //Reserved
      pmb_status_byte[5]   <= pmb_status_vout[7];
      pmb_status_byte[4:3] <= 2'd0; //Reserved
      pmb_status_byte[2]   <= |pmb_status_temperature[7:0];
      pmb_status_byte[1]   <= |pmb_status_cml[7:0]; 
      pmb_status_byte[0]   <= 1'b0; //None of the above is undefined
    end
  end

  always @(posedge sysmon_rst or posedge pmb_clear or posedge DCLK_in) begin
    if(sysmon_rst || pmb_clear)
      pmb_status_temperature <='d0;
    else begin
      pmb_status_temperature[7]   <= pmb_clr_status_temperature[7] ? 0 : (OT_out & !ut_fault); 
      pmb_status_temperature[6]   <= pmb_clr_status_temperature[6] ? 0 : (ALM_out[0] & !ut_warn);
      pmb_status_temperature[5]   <= pmb_clr_status_temperature[5] ? 0 : ut_warn;
      pmb_status_temperature[4]   <= pmb_clr_status_temperature[4] ? 0 : ut_fault;
      pmb_status_temperature[3:0] <= 4'd0;
    end
  end

  always @(posedge sysmon_rst or posedge pmb_clear or posedge DCLK_in) begin
    if(sysmon_rst || pmb_clear)
      pmb_status_vout      <= 'd0;
    else if (pmb_paged) begin
      pmb_status_vout[7]   <= pmb_clr_status_vout[7]? 0: (ALM_out[pmb_page_alm_id] && !alm_ut[pmb_page_alm_id]); //Over voltage
      pmb_status_vout[6:5] <= 'd0; //Reserved
      pmb_status_vout[4]   <= pmb_clr_status_vout[4]? 0: alm_ut[pmb_page_alm_id]; //Under voltage
      pmb_status_vout[3:0] <= 'd0; //Reserved
    end
  end

   always @(posedge sysmon_rst or posedge pmb_clear or posedge DCLK_in) begin
    if(sysmon_rst || pmb_clear) 
      pmb_status_cml      <= 'd0;
    else begin
      pmb_status_cml[7]   <= pmb_clr_status_cml[7] ? 0 : pmb_unsp_cmd;
      pmb_status_cml[6]   <= pmb_clr_status_cml[6] ? 0 : (pmb_unsp_data || pmb_read_only_cmd);
      pmb_status_cml[5:2] <= 'd0; //Reserved 
      pmb_status_cml[1]   <= pmb_clr_status_cml[1] ? 0 : 0; //Other/TBD
      pmb_status_cml[0]   <= 'd0; //Reserved
    end
  end

  always @(posedge sysmon_rst or posedge pmb_clear or posedge DCLK_in) begin
    if(sysmon_rst || pmb_clear ) 
      SMBALERT_TS_out <= 1; // active negative
    else begin
      SMBALERT_TS_out <= !((|pmb_status_word) || (|pmb_status_byte));
    end
  end

  //---- End of PMBus logic ------------------------------------------------

  //---------------------------------------------------------------------
  // Clock divider, generate  and adcclk

  assign adcclk_period_end   = (adcclk_count ==curr_clkdiv_sel-1);
  assign adcclk_period_start = (adcclk_count == 0);

  always @(posedge DCLK_in)
    adcclk_period_end_d <= adcclk_period_end;

  always @(posedge DCLK_in)
    sysclk <= ~sysclk;

  always @(posedge DCLK_in ) begin
    if (curr_clkdiv_sel > 'd2 || adcclk_count_rst) begin
      if ((adcclk_count >= curr_clkdiv_sel-1) || adcclk_count_rst) 
        adcclk_count <= 0;
      else 
        adcclk_count <= adcclk_count + 1;

      if(adcclk_count_rst)
        adcclk_tmp <= 1;
      else if(adcclk_count <= curr_clkdiv_sel/2 -1)
        adcclk_tmp <= 1;
      else
        adcclk_tmp <= 0;
    end 
    else 
      adcclk_tmp <= ~adcclk_tmp;
  end

  assign curr_clkdiv_sel = cfg_reg2[15:8];
  assign adcclk_div1     = (curr_clkdiv_sel > 'd2) ? 0 : 1;
  assign adcclk          = (adcclk_div1) ? ~sysclk : adcclk_tmp;

  // end clock divider    
      
  //----------------------------------------------------------------- 
  // sequence control
  //----------------------------------------------------------------- 


  assign lr_chan_on       = (lr_tot_chan>0)  && cont_seq_mode;
  assign cont_seq_only_hr = (lr_tot_chan==0) && cont_seq_mode;

  
  // CR-961759 When channel selection registers are changed, the update is after end of the sequence.
  // In dual channel, EOS is optional, hence EOS_out is not used.
  always @(posedge sysmon_rst or posedge DCLK_in) begin 
    if( sysmon_rst) 
      add_channel <= 0;
    else begin //it has to be the final EOS of the final channel in the big loop hence tot_final_conversion
      if(eoc_asrt && (!avg_en||avg_final_loop) && tot_final_conversion && (add_channel_hr_p||add_channel_lr_p)) 
        add_channel <= 1;
      else 
        add_channel <= 0;
    end
  end

  always @(posedge sysmon_rst or posedge DCLK_in) begin //at initialization or sequence restart
    if( sysmon_rst) begin 
      for(kk=0; kk<=CONV_CNT_P; kk=kk+1) begin
        seq_hr_mem[kk] = 0;
        seq_lr_mem[kk] = 0;
        hr_tot_chan    = 0;
        lr_tot_chan    = 0;
        lr_calib_on    = 0;
      end
    end
    else if(initialize[1] || add_channel) begin
      lr_calib_on = 0;
      if (single_pass_active || cont_seq_mode) begin   //single pass or continuous sequence mode
        // high rate sequence
        hr_tot_chan = 0;
        for (si=0; (si<= 47&&hr_tot_chan<=31); si=si+1) begin
          if ((seq_hr_chan_reg_comb[si] ==1) //begin
            || (si==0 && seq_hr_chan_reg_comb[0]==0 && single_pass_active))  begin //calibration has to be added to single pass mode if not available
            seq_hr_mem[hr_tot_chan] = si;   
            hr_tot_chan = hr_tot_chan + 1;
            //seq_hr_mem possible max is 33 - 1 = 32 max channels. Max allowed channels are 31.
            if (hr_tot_chan==32)
              $display ("Info: [Unisim %s-60] Max allowed channels are 31. Please check the high rate channel selection (46h,48h,49h). After 31, channels will be ignored.", MODULE_NAME);
          end
        end
        if (cont_seq_mode) begin  
          //review for low rate high rate selection interaction
          lr_tot_chan = 0;
          for (si=0; si<= 47; si=si+1) begin
            if (seq_lr_chan_reg_comb[si] ==1)  begin
              //low rate
              if(seq_lr_chan_reg_comb[si]==seq_hr_chan_reg_comb[si] && !((si>=1 && si<=4)||si==15||(si>=36 && si<=47)) ) begin //CR 863886
                //handle duplicates first
                case (si)
                  6'h00   : begin
                              $display ("Info: [Unisim %s-29] In attribute INIT_7A[0],   Calibration has already been selected for the ADC channel sequence with INIT_48[0]. It will be ignored in the low rate sequence.", MODULE_NAME);
                              lr_calib_on=0;
                            end
                  6'h05   : $display ("Info: [Unisim %s-30] In attribute INIT_7A[5],   VCC_PSAUX has already been selected for the ADC channel sequence with INIT_48[0]. It will be ignored in the low rate sequence.", MODULE_NAME);
                  6'h06   : $display ("Info: [Unisim %s-31] In attribute INIT_7A[6],   VCC_PSINTFP has already been selected for the ADC channel sequence with INIT_48[0]. It will be ignored in the low rate sequence.", MODULE_NAME);
                  6'h07   : $display ("Info: [Unisim %s-32] In attribute INIT_7A[7],   VCC_PSINTLP has already been selected for the ADC channel sequence with INIT_48[0]. It will be ignored in the low rate sequence.", MODULE_NAME);
                  6'h08   : $display ("Info: [Unisim %s-33] In attribute INIT_7A[8],   TEMPERATURE has already been selected for the ADC channel sequence with INIT_48[8]. It will be ignored in the low rate sequence.", MODULE_NAME);
                  6'h09   : $display ("Info: [Unisim %s-34] In attribute INIT_7A[9],   INT_AVG has already been selected for the ADC channel sequence with INIT_48[9]. It will be ignored in the low rate sequence.", MODULE_NAME);
                  6'h0A   : $display ("Info: [Unisim %s-35] In attribute INIT_7A[10],  AUX_AVG has already been selected for the ADC channel sequence with INIT_48[10]. It will be ignored in the low rate sequence.", MODULE_NAME);
                  6'h0B   : $display ("Info: [Unisim %s-36] In attribute INIT_7A[11],  VpVn has already been selected for the ADC channel sequence with INIT_48[11]. It will be ignored in the low rate sequence.", MODULE_NAME);
                  6'h0C   : $display ("Info: [Unisim %s-37] In attribute INIT_7A[12],  VREFP has already been selected for the ADC channel sequence with INIT_48[12]. It will be ignored in the low rate sequence.", MODULE_NAME);
                  6'h0D   : $display ("Info: [Unisim %s-38] In attribute INIT_7A[13],  VREFN has already been selected for the ADC channel sequence with INIT_48[13]. It will be ignored in the low rate sequence.", MODULE_NAME);
                  6'h0E   : $display ("Info: [Unisim %s-39] In attribute INIT_7A[14],  BRAM has already been selected for the ADC channel sequence with INIT_48[14]. It will be ignored in the low rate sequence.", MODULE_NAME);
                  6'h10, 6'h11, 6'h12, 6'h13, 6'h14, 6'h15, 6'h16, 6'h17,6'h18, 6'h19, 6'h1A, 6'h1B,6'h1C, 6'h1D, 6'h1E, 6'h1F   : 
                            $display ("Info: [Unisim %s-41] In attribute INIT_7B[%0d], auxiliary analog input has already been selected for the ADC channel sequence with INIT_49[%0d]. It will be ignored in the low rate sequence.", MODULE_NAME, (si-16), (si-16));
                  6'h20   : $display ("Info: [Unisim %s-42] In attribute INIT_7C[0],   USER0 has already been selected for the ADC channel sequence with INIT_46[0]. It will be ignored in the low rate sequence.", MODULE_NAME);
                  6'h21   : $display ("Info: [Unisim %s-43] In attribute INIT_7C[1],   USER1 has already been selected for the ADC channel sequence with INIT_46[1]. It will be ignored in the low rate sequence.", MODULE_NAME);
                  6'h22   : $display ("Info: [Unisim %s-44] In attribute INIT_7C[2],   USER2 has already been selected for the ADC channel sequence with INIT_46[2]. It will be ignored in the low rate sequence.", MODULE_NAME);
                  6'h23   : $display ("Info: [Unisim %s-45] In attribute INIT_7C[3],   USER3 has already been selected for the ADC channel sequence with INIT_46[3]. It will be ignored in the low rate sequence.", MODULE_NAME);
                  default : $display ("Info: [Unisim %s-40] In attribute INIT_7A, INIT_7B or INIT_7C, same selections have already been selected for the ADC channel sequence with INIT_46[],INIT_48[], or INIT_49[]. They will be ignored in the low rate sequence.", MODULE_NAME);
                endcase
              end
              else begin  
                //not duplicate in low and high rate, only in low rate. stays as is.
                seq_lr_mem[lr_tot_chan] = si;   //seq_lr_mem possible max is 33 - 1 = 32 max channels. Max allowed channels are 31.
                lr_tot_chan = lr_tot_chan + 1;
                if(si==0 && seq_lr_chan_reg_comb[0]==1)
                  lr_calib_on = 1;
              end
            end
            else if(seq_hr_chan_reg_comb[si]==0 &&(si==0 || si==8)) begin 
              // handle missing ones
              // seq_lr_chan_reg_comb[si]==0. Calibration and temperature are disabled in both by the user 
              seq_lr_mem[lr_tot_chan] = si;   
              lr_tot_chan = lr_tot_chan + 1;
              if(si==0) begin
                lr_calib_on = 1;
                $display ("Info: [Unisim %s-51] Neither attribute INIT_7A[0] nor INIT_48[0] have been selected. Calibration will be enabled in the low rate sequence anyway.", MODULE_NAME);
              end
              else //si==8
                $display ("Info: [Unisim %s-52] Neither attribute INIT_7A[8] nor INIT_48[8] have been selected. Temperature will be enabled in the low rate sequence anyway.", MODULE_NAME);
            end
          end
        end //for   
        if(hr_tot_chan==0) begin
          $display ("Error: [Unisim %s-65] No channel was selected for HR. This is not a valid option. Simulation exiting.", MODULE_NAME);
          #1 $finish;
        end
      end //cont_seq_mode for low rate
      else if (default_mode ) begin //default mode
        if(ext_mux) 
          $display("Info: [Unisim %s-50] External mux selection will be disregarded as SYSMON is in default mode. Instance: %m", MODULE_NAME);

        if (SIM_DEVICE == "ULTRASCALE_PLUS" || SIM_DEVICE == "ULTRASCALE_PLUS_ES1" || SIM_DEVICE == "ULTRASCALE_PLUS_ES2") begin
          hr_tot_chan = 5;
          seq_hr_mem[0] = 0;
          seq_hr_mem[1] = 8;
          seq_hr_mem[2] = 9;
          seq_hr_mem[3] = 10;
          seq_hr_mem[4] = 14;
        end
        else if (SIM_DEVICE == "ZYNQ_ULTRASCALE" || SIM_DEVICE == "ZYNQ_ULTRASCALE_ES1" || SIM_DEVICE == "ZYNQ_ULTRASCALE_ES2") begin
          hr_tot_chan = 8;
          seq_hr_mem[0] = 0;
          seq_hr_mem[1] = 5;
          seq_hr_mem[2] = 6;
          seq_hr_mem[3] = 7;
          seq_hr_mem[4] = 8;
          seq_hr_mem[5] = 9;
          seq_hr_mem[6] = 10;
          seq_hr_mem[7] = 14;
        end
      end // default_mode
      else if(single_chan_mode && ext_mux)
        $display("Info: [Unisim %s-50] External mux selection will be disregarded as SYSMON is in single channel mode. Instance: %m", MODULE_NAME);
    end //initialize[1] || add_channel
  end //always

  wire [15:0] chan_avg_hr_reg1;
  wire [15:0] chan_avg_hr_reg2;
  wire [15:0] chan_avg_hr_reg3;
  wire [47:0] seq_avg_hr_reg_comb ;
  wire        chan_avg_hr_set;

  wire [15:0] chan_avg_lr_reg1;
  wire [15:0] chan_avg_lr_reg2;
  wire [15:0] chan_avg_lr_reg3;
  wire [47:0] seq_avg_lr_reg_comb;
  wire        chan_avg_lr_set;
  
  assign chan_avg_hr_reg1 = seq_hr_chan_reg1 & seq_avg_reg1;
  assign chan_avg_hr_reg2 = seq_hr_chan_reg2 & seq_avg_reg2;
  assign chan_avg_hr_reg3 = seq_hr_chan_reg3 & seq_avg_reg3;
  assign seq_avg_hr_reg_comb = {chan_avg_hr_reg3, chan_avg_hr_reg2, chan_avg_hr_reg1};
  assign chan_avg_hr_set  = |seq_avg_hr_reg_comb;

  assign chan_avg_lr_reg1 = seq_lr_chan_reg1 & seq_avg_reg1;
  assign chan_avg_lr_reg2 = seq_lr_chan_reg2 & seq_avg_reg2;
  assign chan_avg_lr_reg3 = seq_lr_chan_reg3 & seq_avg_reg3;
  assign seq_avg_lr_reg_comb = {chan_avg_lr_reg3, chan_avg_lr_reg2, chan_avg_lr_reg1};
  assign chan_avg_lr_set  = |seq_avg_lr_reg_comb;
   
  //hr_lr_tot_per is the total period of the combined high and low rate sequences
  assign int_tot_per    = (hr_tot_chan * (4 ** lr_rate)) +1;
  assign hr_lr_tot_per  = lr_chan_on ? (int_tot_per * lr_tot_chan) : hr_tot_chan ;
  assign tot_per        = cont_seq_mode ? hr_lr_tot_per: 
                          (single_pass_active|| default_mode) ?  hr_tot_chan :
                          1; //single_chan_mode 
                          // or in unknown mode just calibrate

  // CR-961533
  // When SLOW_SEQ or SLOW_EOS are changed dynamically, the change should take place 
  // after mode change as per rtl design.
  always @(posedge DCLK_in or posedge sysmon_rst) begin 
    if (sysmon_rst) begin
      lr_eos        <= 0;
      lr_rate       <= 0;
    end
    else if(initialize[0]) begin
      lr_eos[1:0]   <= cfg_reg4[11:10];
      lr_rate[1:0]  <= cfg_reg4[9:8];
    end
  end

  integer conv_tot_count;
  integer conv_hr_count;
  integer conv_lr_count;
  wire [15:0] conv_hr_count_p;
  wire [15:0] conv_lr_count_p;
  integer avg_loop_count_hr;
  integer avg_loop_count_lr;

  assign  avg_final_loop           = (!avg_en)  ||
                                     (!avg_cur) ||
                                     (avg_final_loop_hr && !seq_lr_selected) || 
                                     (avg_final_loop_lr && seq_lr_selected) ;
  assign  avg_final_loop_hr        = (avg_loop_count_hr == avg_amount);
  assign  avg_final_loop_lr        = (avg_loop_count_lr == avg_amount);

  always @(posedge DCLK_in or posedge sysmon_rst) begin
    if(sysmon_rst) begin
      conversion_before_calib <= 0;
      hr_final_conversion     <= 0;
      tot_final_conversion    <= 0;
      lr_final_conversion     <= 0;
    end
    else begin
      if(adc_state==ST_A_CALIB || adc_state==ST_A_FIRST_CALIB) begin
        conversion_before_calib <= 0;
        hr_final_conversion     <= 0;
        tot_final_conversion    <= 0;
        lr_final_conversion     <= 0;
      end
      else if(conv_track)begin //check
        conversion_before_calib <= (CHANNEL_out!=8) &&
                                   ~(event_driven_mode && single_pass_mode) &&
                                   ((lr_chan_on && 
                                   ((~lr_calib_on && conv_hr_count==hr_tot_chan-1 && seq_lr_selected) || 
                                   ( lr_calib_on && conv_tot_count==tot_per-1))) ||
                                   (!lr_chan_on && conv_hr_count==hr_tot_chan-1) );
        hr_final_conversion     <= (((hr_tot_chan==1 && !lr_calib_on) || CHANNEL_out!=8) && (conv_hr_count==hr_tot_chan-1)) ||
                                   (single_chan_mode && CHANNEL_out!=8); 
        tot_final_conversion    <= (CHANNEL_out!=8) &&(conv_tot_count==tot_per-1);
        lr_final_conversion     <= (~lr_calib_on && conv_tot_count==tot_per-1) || 
                                  (lr_calib_on && lr_tot_chan>1 && conv_tot_count==tot_per-int_tot_per) ||
                                  (lr_calib_on && lr_tot_chan==1);
      end
    end
  end //always


  assign seq_lr_selected_p  =  lr_chan_on && //!seq_lr_selected &&
                               ((lr_calib_on && ( conv_tot_count   %int_tot_per)==int_tot_per-1) || //calibration being always on puts lr on first if calib is on lr channel.
                               (!lr_calib_on&& ( conv_tot_count   %int_tot_per)==int_tot_per-2) ); //otherwise it is the last

  //pre calculate
  assign conv_hr_count_p = (conv_hr_count < hr_tot_chan-1) ? (conv_hr_count+1) : (event_driven_mode && single_pass_mode) ? 1 : 0;
  assign conv_lr_count_p  = (conv_lr_count < lr_tot_chan-1) ? (conv_lr_count+1) : 0;

  always @(posedge sysmon_rst or posedge initialize[2] or posedge chan_asrt_1) begin
    if(sysmon_rst) begin
      conv_tot_count    <= 0;
      conv_hr_count     <= 0;
      conv_lr_count     <= 0;
      seq_lr_selected   <= 0;
    end
    else begin
      if( initialize[2] ) begin
        conv_tot_count      <= 0;
        if(cont_seq_mode && lr_calib_on) begin
          seq_lr_selected   <= 1;
          conv_hr_count     <= 0;
          conv_lr_count     <= 0;
        end
        else begin
          seq_lr_selected   <= 0;
          conv_hr_count     <= 0;
          conv_lr_count     <= 0;
        end
      end
      else if(chan_asrt_1 ) begin 
        //increase counters
        if (conv_tot_count<tot_per-1) 
          conv_tot_count <= conv_tot_count+1;
        else begin
          conv_tot_count <= 0;
        end

        if(seq_lr_selected) begin
          if(conv_lr_count < lr_tot_chan-1)
            conv_lr_count <= conv_lr_count +1;
          else
            conv_lr_count <= 0;
        end

        if(!seq_lr_selected_p && !(seq_lr_selected && lr_calib_on && st_first_calib_chan)) begin
          if(conv_hr_count < hr_tot_chan-1)
            conv_hr_count <= conv_hr_count +1;
          else if(event_driven_mode && single_pass_mode)
            conv_hr_count <= 1;
          else 
            conv_hr_count <= 0;
        end

        if(seq_lr_selected) 
          seq_lr_selected <= 0;
        else if ( lr_chan_on && 
                ((lr_calib_on && (conv_tot_count%int_tot_per)==int_tot_per-1) || //calibration being always on puts lr on first if calib is on lr channel.
                 (!lr_calib_on&& (conv_tot_count%int_tot_per)==int_tot_per-2)   ) //otherwise it is the last
               )
          seq_lr_selected <= 1;
      end
    end
  end //always

  //align seq_lr_selected to chan_asrt_3, delay 2 DCLK_in cycles
  always @(posedge DCLK_in or posedge sysmon_rst) begin
    if(sysmon_rst) 
      seq_lr_selected_d <= 0;
    else 
      seq_lr_selected_d <= {seq_lr_selected_d[0], seq_lr_selected};
  end
  

  always @(posedge DCLK_in or posedge sysmon_rst) begin
    if(sysmon_rst) begin
      avg_loop_count_lr <= 0;
      avg_loop_count_hr <= 0;
    end
    else begin
      if( initialize[2] ) begin
        avg_loop_count_lr <= 0;
        avg_loop_count_hr <= 0;
      end
      else if(chan_asrt_3 ) begin
        if(!seq_lr_selected_d[1] && hr_final_conversion) begin
          if(single_pass_mode || !avg_en || ( avg_en && avg_loop_count_hr == avg_amount))
            avg_loop_count_hr <= 0; 
          else 
            avg_loop_count_hr <= avg_loop_count_hr +1; 
        end

        if(seq_lr_selected_d[1] && lr_final_conversion)  begin
          if(!avg_en || (avg_en && avg_loop_count_lr == avg_amount))
            avg_loop_count_lr <= 0; 
          else 
            avg_loop_count_lr <= avg_loop_count_lr +1; 
        end

      end
    end
  end //always

  always @(posedge sysmon_rst or posedge initialize[2] or posedge chan_asrt_2) begin
    if(sysmon_rst) begin
      chan_reg_id_cur  <= 0;
      chan_out_id_cur  <= 8;
      acq_ext_cur      <= 0;
      bipolar_cur      <= 0; 
      avg_cur          <= 0;
      chan_reg_id_next <= 0;
      chan_out_id_next <= 8;
      acq_ext_next     <= 0;
      bipolar_next     <= 0; 
      avg_next         <= 0;
    end
    else if(initialize[2] )begin
      chan_reg_id_cur  <= 0;
      chan_out_id_cur  <= 8;
      acq_ext_cur      <= 0;
      bipolar_cur      <= 0; 
      avg_cur          <= 0;
      if(cont_seq_mode ||single_pass_active ||default_mode) begin
        if(cont_seq_mode && lr_calib_on) begin
          chan_reg_id_next <= seq_hr_mem[0];
          chan_out_id_next <= conv_combregid_to_chanout(seq_hr_mem[0]);
          acq_ext_next     <= seq_acq_ext_reg_comb[seq_hr_mem[0]];
          bipolar_next     <= seq_bipolar_reg_comb[seq_hr_mem[0]];
          avg_next         <= avg_en ? seq_avg_hr_reg_comb[seq_hr_mem[0]] : 0;
        end
        else if(cont_seq_mode && lr_chan_on && int_tot_per==2 ) begin //same as lr_rate==LR_EVERY_OTHER && hr_tot_chan==1
          chan_reg_id_next <= seq_lr_mem[0];
          chan_out_id_next <= conv_combregid_to_chanout(seq_lr_mem[0]);
          acq_ext_next     <= seq_acq_ext_reg_comb[seq_lr_mem[0]];
          bipolar_next     <= seq_bipolar_reg_comb[seq_lr_mem[0]];
          avg_next         <= seq_avg_lr_reg_comb[seq_lr_mem[0]];
        end
        else begin //single_pass_active, default_mode, or cont_seq_mode with next one on hr channel
          chan_reg_id_next <= seq_hr_mem[1];
          chan_out_id_next <= conv_combregid_to_chanout(seq_hr_mem[1]);
          acq_ext_next     <= seq_acq_ext_reg_comb[seq_hr_mem[1]];
          bipolar_next     <= seq_bipolar_reg_comb[seq_hr_mem[1]];
          avg_next         <= avg_en ? (default_mode ? 1: seq_avg_hr_reg_comb[seq_hr_mem[1]]) : 0;
        end
      end
      else if(single_chan_mode) begin
        //first 8, then the same channel continuously
        chan_reg_id_next <= conv_combregid_to_chanout(single_chan_id);
        chan_out_id_next <= single_chan_id;
        // For single channel the user doesn't have to select via control registers. 
        // However acquisition extension and bipolar mode are only available to analog channels. 
        if(single_chan_id==3 || (single_chan_id>=16 && single_chan_id<=31)) begin
          acq_ext_next     <= acq_ext; 
          bipolar_next     <= bipolar_mode; 
        end
        else begin
          acq_ext_next     <= 0;
          bipolar_next     <= 0;
          if(acq_ext || bipolar_mode)
            $display("Info: [Unisim %s-68] In single channel mode, acquisition extension or bipolar mode cannot be enabled for non-analog channels. They will be ignored. Instance: %m", MODULE_NAME);
        end
        avg_next         <= avg_en;
      end

    end //initialization

    else if(chan_asrt_2) begin
                  
      //Update current *_cur <=*_next;
      chan_reg_id_cur  <= chan_reg_id_next;
      chan_out_id_cur  <= chan_out_id_next;
      acq_ext_cur      <= acq_ext_next;
      bipolar_cur      <= bipolar_next;
      avg_cur          <= avg_next;

      //Update *_next
      if(single_pass_active  || 
        default_mode || 
        cont_seq_only_hr ||
        (lr_chan_on && !seq_lr_selected_p)
        ) begin
        chan_reg_id_next <= seq_hr_mem[conv_hr_count_p];
        chan_out_id_next <= conv_combregid_to_chanout(seq_hr_mem[conv_hr_count_p]);
        acq_ext_next     <= seq_acq_ext_reg_comb[seq_hr_mem[conv_hr_count_p]];
        bipolar_next     <= seq_bipolar_reg_comb[seq_hr_mem[conv_hr_count_p]];
        avg_next         <= avg_en ? (default_mode ? 1: seq_avg_hr_reg_comb[seq_hr_mem[conv_hr_count_p]]) : 0;
      end
      else if (cont_seq_mode) begin// lr_tot_chan>0 && seq_lr_selected
        chan_reg_id_next <= seq_lr_mem[conv_lr_count];
        chan_out_id_next <= conv_combregid_to_chanout(seq_lr_mem[conv_lr_count]);
        acq_ext_next     <= seq_acq_ext_reg_comb[seq_lr_mem[conv_lr_count]];
        bipolar_next     <= seq_bipolar_reg_comb[seq_lr_mem[conv_lr_count]];
        avg_next         <= avg_en ? seq_avg_lr_reg_comb[seq_lr_mem[conv_lr_count]] : 0 ;
      end
      //else if single_chan_mode: in single channel mode no need to update the next. 
      
    end
  end

 
  //-----------------------------------------------------------
  // EOC and EOS
  //-----------------------------------------------------------

  always @(posedge DCLK_in or posedge sysmon_rst) begin
    if(sysmon_rst) begin
      EOC_out <= 0;
      EOS_out <= 0;
    end
    else begin
      if(eoc_asrt && (!avg_en || !avg_cur || (avg_en && avg_cur && avg_final_loop) ) ) begin
        EOC_out <= 1;
        if(((!lr_chan_on && hr_final_conversion) ||  // eos selection is available only when lr chan is active. otherwise always on.
           (lr_chan_on && hr_final_conversion && !seq_lr_selected &&  lr_eos!=LR_EOS_LR_ONLY) || //hr
           (lr_chan_on && lr_final_conversion && seq_lr_selected && (lr_eos==LR_EOS_HR_LR || lr_eos==LR_EOS_LR_ONLY)) //lr
           )  && !single_chan_mode) //CR-1049898
          EOS_out <= 1;
        else
          EOS_out <= 0;
      end
      else begin
        EOC_out <= 0;
        EOS_out <= 0;
      end
    end
  end


    

//-----------------------------------------------------
// Conversion
//-----------------------------------------------------

  always @(posedge sysmon_rst or posedge chan_asrt_1) begin
    if (sysmon_rst == 1) begin
      mn_mux_in <= 0.0;
    end
    else if(chan_asrt_1) begin
      if ( chan_out_id_next == 7  || (chan_out_id_next >= 9 && chan_out_id_next <= 12) || chan_out_id_next >= 36)
        $display("Warning: [Unisim %s-14] The analog channel %x at time %.3f ns is invalid. Check register 40h[5:0]. Instance: %m", MODULE_NAME, chan_out_id_next, $time/1000.0);
      //K else if(bipolar_next) begin //can only be enabled for channels 3,16-31
      else if ((chan_out_id_next == 3) || (chan_out_id_next >= 16 && chan_out_id_next <= 31)) begin
        if (ext_mux_en) begin
          tmp_v = $bitstoreal(mn_in_diff[ext_mux_chan_id]);
          mn_mux_in <= tmp_v; 
        end
        else begin
          tmp_v = $bitstoreal(mn_in_diff[chan_out_id_next]);
          mn_mux_in <= tmp_v; 
        end
      end
      else 
        mn_mux_in <= $bitstoreal(mn_in_uni[chan_out_id_next]);
        
    end //chan_asrt_1
  end //always
    
  // Check if (Vp+Vn)/2 = 0.5 +/- 100 mv,  unipolar only
  //always @(posedge DCLK_in or posedge sysmon_rst ) begin
  always @(posedge chan_asrt_3 ) begin
    if (!sysmon_rst)
      if( chan_asrt_3 && !bipolar_mode && ((chan_out_id_cur == 3) || (chan_out_id_cur >= 16 && chan_out_id_cur <= 31))) begin  
        chan_val_p_tmp = $bitstoreal(chan_val_tmp [chan_out_id_cur]);
        chan_val_n_tmp = $bitstoreal(chan_valn_tmp[chan_out_id_cur]);

        if (!bipolar_cur &&( chan_val_n_tmp > chan_val_p_tmp))
          $display("Warning: [Unisim %s-8] The N input for external channel %x must be smaller than P input when in unipolar mode. (P=%0.2f N=%0.2f) at %.3f ns. Instance: %m", MODULE_NAME, chan_out_id_cur, chan_val_p_tmp, chan_val_n_tmp, $time/1000.0);
        if (!bipolar_cur &&( chan_val_n_tmp > 0.5 || chan_val_n_tmp < 0.0))
          $display("Warning: [Unisim %s-9] The range of N input for external channel %x should be between 0V to 0.5V when in unipolar mode. (N=%0.2f) at %.3f ns. Instance: %m", MODULE_NAME, chan_out_id_cur, chan_val_n_tmp, $time/1000.0);
        if (bipolar_cur && (((chan_val_p_tmp-chan_val_n_tmp) > 0.5)|| ((chan_val_p_tmp-chan_val_n_tmp) <-0.5)))
          $display("Warning: [Unisim %s-56] Vp-Vn for external channel %x must be in [-0.5,0.5] V range when in bipolar mode. (P=%0.2f N=%0.2f ) at %.3f ns. Instance: %m", MODULE_NAME, chan_out_id_cur, chan_val_p_tmp, chan_val_n_tmp, $time/1000.0);
      end
  end


  always @(posedge chan_asrt_3) begin
    if (chan_out_id_cur == 0) begin    // adc temperature conversion
      if(SIM_DEVICE=="ULTRASCALE_PLUS" || SIM_DEVICE=="ZYNQ_ULTRASCALE" || SIM_DEVICE=="ULTRASCALE_PLUS_ES2" || SIM_DEVICE=="ZYNQ_ULTRASCALE_ES2")
        adc_temp_result = (mn_mux_in + 280.2308787) * 0.00196343 * 65535.0; //CR 961722 10/20/2016. Internal reference
      else // ES1
        adc_temp_result = (mn_mux_in + 273.15) * 0.00203580 * 65535.0; //CR 912341  

      if (adc_temp_result >= 65535.0)
        conv_result_int = 65535;
      else if (adc_temp_result < 0.0)
        conv_result_int = 0;
      else begin
        conv_result_int = $rtoi(adc_temp_result);
        if (adc_temp_result - conv_result_int > 0.9999)
          conv_result_int = conv_result_int + 1;
      end
    end
    else if (chan_out_id_cur == 1 || chan_out_id_cur == 2 || chan_out_id_cur ==6 ||
             chan_out_id_cur == 13 || chan_out_id_cur == 14 || chan_out_id_cur ==  15 || 
             (chan_out_id_cur >= 32 && chan_out_id_cur <= 35)) begin     // internal power conversion

      if((chan_out_id_cur >= 32 && chan_out_id_cur <= 35) && 
         bank_sel_6V[chan_out_id_cur-32]==1) // CR 949547
        adc_intpwr_result = mn_mux_in * 65536.0 / 6.0; //6V range is selected, only available for VUSER ports
      else
        adc_intpwr_result = mn_mux_in * 65536.0 / 3.0; //3V range, hence divide by 3

      if (adc_intpwr_result >= 65535.0) // max value is 'hFFFF
        conv_result_int = 65535;
      else if (adc_intpwr_result < 0.0) // min value is 0
        conv_result_int = 0;
      else begin
        conv_result_int = $rtoi(adc_intpwr_result);
        if (adc_intpwr_result - conv_result_int > 0.9999)
          conv_result_int = conv_result_int + 1;
      end
    end
    else if (chan_out_id_cur == 3 || (chan_out_id_cur >=16 && chan_out_id_cur <= 31)) begin
      adc_ext_result =  (mn_mux_in) * 65536.0 ; //1V input range, hence divide by 1
      if (bipolar_cur == 1) begin //bipolar maps -0.5V to 0.5V to -32768-32767 range
        if (adc_ext_result > 32767.0) //+0.5V
          conv_result_int = 32767;
        else if (adc_ext_result < -32768.0) //-0.5V
          conv_result_int = -32768;
        else begin
          conv_result_int = $rtoi(adc_ext_result);
          if (adc_ext_result - conv_result_int > 0.9999)
             conv_result_int = conv_result_int + 1;
        end
      end
      else begin //unipolar maps 0V to 1V to 0-65535 range
        if (adc_ext_result > 65535.0)
          conv_result_int = 65535;
        else if (adc_ext_result < 0.0)
          conv_result_int = 0;
        else begin
          conv_result_int = $rtoi(adc_ext_result);
          if (adc_ext_result - conv_result_int > 0.9999)
             conv_result_int = conv_result_int + 1;
        end
      end
    end
    else begin //invalid channel
      conv_result_int = 0;
    end

    conv_result = conv_result_int;
    
  end // always 

  always @(posedge DCLK_in or  posedge sysmon_rst) begin
    if (sysmon_rst == 1)
      conv_result_reg <= 0;
    else begin
      if (chan_asrt_4)
        conv_result_reg <= conv_result;
    end
  end

    
  //---------------------------------------------------------
  // average
  //---------------------------------------------------------
  assign averaging  = default_mode ? 2'b01 : cfg_reg0[13:12]; 
  assign avg_amount = averaging==2'b00 ? 0   :
                      averaging==2'b01 ? 15  :
                      averaging==2'b10 ? 63  :
                      averaging==2'b11 ? 255 :
                      0;

  // In continuous mode, at least 1 channel in HR or LR should have averaging
  // enabled so that averaging is practically enabled.
  assign avg_en     = single_pass_mode ? 0 :
                      default_mode ? 1 : 
                      (averaging!=2'b00 && (single_chan_mode || chan_avg_hr_set || chan_avg_lr_set));

  always @(posedge DCLK_in or posedge sysmon_rst) begin 
    if (sysmon_rst) begin
      conv_acc_result = 16'd0;
      conv_acc_vec    = 24'd0;
      for (j = 0; j <= 63; j = j + 1) 
        conv_acc[j] = 0;
    end
    else  begin
     if(EOC_out==1 && avg_cur && avg_final_loop) begin
        conv_acc_result = 16'd0;
        conv_acc_vec    = 24'd0;
        conv_acc[chan_out_id_cur] = 0;
     end
     else if (chan_asrt_4 && avg_cur) begin
       conv_acc[chan_out_id_cur] = conv_acc[chan_out_id_cur] + conv_result_int;

       conv_acc_vec              = conv_acc[chan_out_id_cur];

       case (averaging)
         2'b00 : conv_acc_result = 16'd0;
         2'b01 : conv_acc_result = conv_acc_vec[19:4];
         2'b10 : conv_acc_result = conv_acc_vec[21:6];
         2'b11 : conv_acc_result = conv_acc_vec[23:8];
       endcase 
     end 
    end // if (sysmon_rst == 0)
  end 

  // end average    
        

  always @( posedge DCLK_in or posedge alm_rst or posedge gsr_in ) begin
    if(alm_rst ==1 || gsr_in==1) begin
      data_reg[32]  = 16'h0000;
      data_reg[33]  = 16'h0000;
      data_reg[34]  = 16'h0000;
      data_reg[35]  = 16'h0000;
      data_reg[36]  = 16'hFFFF;
      data_reg[37]  = 16'hFFFF;
      data_reg[38]  = 16'hFFFF;
      data_reg[39]  = 16'hFFFF;
      data_reg[40]  = 16'h0000;
      data_reg[41]  = 16'h0000;
      data_reg[42]  = 16'h0000;
      data_reg[44]  = 16'hFFFF;
      data_reg[45]  = 16'hFFFF;
      data_reg[46]  = 16'hFFFF;
      dr_sram [160] = 16'h0000;
      dr_sram [161] = 16'h0000;
      dr_sram [162] = 16'h0000;
      dr_sram [163] = 16'h0000;
      dr_sram [168] = 16'hFFFF;
      dr_sram [169] = 16'hFFFF;
      dr_sram [170] = 16'hFFFF;
      dr_sram [171] = 16'hFFFF;
    end 
    else if (alm_asrt && avg_final_loop) begin 
      // current or averaged values' update to status registers
      if ((chan_out_id_cur >= 0 && chan_out_id_cur <= 3)  || (chan_out_id_cur == 6) ||
          (chan_out_id_cur >= 13 && chan_out_id_cur <= 31)) begin
        if (avg_cur == 0)
          data_reg[chan_out_id_cur] <= conv_result_reg;
        else if(avg_final_loop)
          data_reg[chan_out_id_cur] <= conv_acc_result;
      end
      else if (chan_out_id_cur >= 32 && chan_out_id_cur <= 35) begin //VUser0-3
        if (avg_cur == 0)
          dr_sram[chan_out_id_cur + 96] <= conv_result_reg; //80h-83h
        else if(avg_final_loop)
          dr_sram[chan_out_id_cur + 96] <= conv_acc_result;
      end
      else if (chan_out_id_cur == 4) // VREFP
        data_reg[chan_out_id_cur] <= 16'h0000; // CR-961722 Simulation always simulates the internal reference behavior. Hence VrefP=0V
      else if (chan_out_id_cur == 5) // VREFN
        data_reg[chan_out_id_cur] <= 16'h0000;

      //min and max values' update
      if (chan_out_id_cur == 0 || chan_out_id_cur == 1 || chan_out_id_cur == 2) begin //TEMPERATURE, VCCINT and VCCAUX max and min
        if (avg_cur == 0) begin
          if (conv_result_reg > data_reg[32 + chan_out_id_cur])
            data_reg[32 + chan_out_id_cur] <= conv_result_reg;
          if (conv_result_reg < data_reg[36 + chan_out_id_cur])
            data_reg[36 + chan_out_id_cur] <= conv_result_reg;
        end
        else if(avg_final_loop) begin
          if (conv_acc_result > data_reg[32 + chan_out_id_cur])
            data_reg[32 + chan_out_id_cur] <= conv_acc_result;
          if (conv_acc_result < data_reg[36 + chan_out_id_cur])
            data_reg[36 + chan_out_id_cur] <= conv_acc_result;
        end  
      end

      else if (chan_out_id_cur == 6) begin //VCCBRAM max and min
        if (avg_cur == 0) begin
          if (conv_result_reg > data_reg[35])
            data_reg[35] <= conv_result_reg;
          if (conv_result_reg < data_reg[39])
            data_reg[39] <= conv_result_reg;
        end
        else if(avg_final_loop) begin
          if (conv_acc_result > data_reg[35])
            data_reg[35] <= conv_acc_result;
          if (conv_acc_result < data_reg[39])
            data_reg[39] <= conv_acc_result;
        end
      end
      else if (chan_out_id_cur >= 13 && chan_out_id_cur <= 15) begin  // VPSINTLP, VPSINTFP , VPSAUX
        if (avg_cur == 0) begin
          if (conv_result_reg > data_reg[27+chan_out_id_cur])
            data_reg[27+chan_out_id_cur] <= conv_result_reg;
          if (conv_result_reg < data_reg[31+chan_out_id_cur])
            data_reg[31+chan_out_id_cur] <= conv_result_reg;
        end
        else if(avg_final_loop) begin
          if (conv_acc_result > data_reg[27+chan_out_id_cur])
            data_reg[27+chan_out_id_cur] <= conv_acc_result;
          if (conv_acc_result < data_reg[31+chan_out_id_cur])
            data_reg[31+chan_out_id_cur] <= conv_acc_result;
        end
      end
      else if (chan_out_id_cur >= 32 && chan_out_id_cur <=35) begin   //Vuser0-3
        if (avg_cur == 0) begin
          if (conv_result_reg < dr_sram[chan_out_id_cur+136])
            dr_sram[chan_out_id_cur+136] <= conv_result_reg;
          if (conv_result_reg > dr_sram[chan_out_id_cur+128])
            dr_sram[chan_out_id_cur+128] <= conv_result_reg;
        end
        else if(avg_final_loop) begin
          if (conv_acc_result < dr_sram[chan_out_id_cur+136])
            dr_sram[chan_out_id_cur+136] <= conv_acc_result;
          if (conv_acc_result > dr_sram[chan_out_id_cur+128])
            dr_sram[chan_out_id_cur+128] <= conv_acc_result;
        end
      end

    end //  ( rst_lock == 0)
  end//always


  always @(posedge DCLK_in or posedge sysmon_rst) begin
    if(sysmon_rst)
      data_written <= 0;
    else if(chan_asrt_5)  begin
      if (avg_cur) 
        data_written <= conv_acc_result;
      else
        data_written <= conv_result_reg;
    end
  end

  always @( posedge DCLK_in or posedge alm_rst or posedge gsr_in ) begin
    if(alm_rst ==1 || gsr_in==1) begin
      ot_out_reg  <= 0;
      alm_out_reg <= 8'b0;
    end
    else if (alm_asrt && avg_final_loop) begin
      if (chan_out_id_cur == 0) begin // temperature 
        if (data_written[15:4] >= ot_limit_reg[15:4]) begin
          ot_out_reg <= 1;
        end else if (dr_sram[8'h57][0] == 1'b1) begin 
          if (data_written[15:1] < dr_sram[8'h57][15:1]) begin
            ot_out_reg <= 1;
          end else begin
            ot_out_reg <= 0;
          end
        end else if (data_written[15:1] < dr_sram[8'h57][15:1]) begin
          ot_out_reg <= 0;
        end

        if (data_written > dr_sram[8'h50]) begin
          alm_out_reg[0] <= 1;
        end else if (dr_sram[8'h54][0] == 1'b1) begin
          if (data_written[15:1] < dr_sram[8'h54][15:1]) begin
            alm_out_reg[0] <= 1;
          end else begin
            alm_out_reg[0] <= 0;
          end
        end else if (data_written[15:1] < dr_sram[8'h54][15:1]) begin
          alm_out_reg[0] <= 0;
        end
      end
   
      if (chan_out_id_cur == 1) begin // VCC INT
        if (data_written > dr_sram[8'h51] || data_written < dr_sram[8'h55])
          alm_out_reg[1] <= 1;
        else
          alm_out_reg[1] <= 0;
      end

      if (chan_out_id_cur == 2) begin //VCCAUX
        if (data_written > dr_sram[8'h52] || data_written < dr_sram[8'h56])
          alm_out_reg[2] <= 1;
        else
          alm_out_reg[2] <= 0;
      end

      if (chan_out_id_cur == 6) begin // VCC BRAM
        if (data_written > dr_sram[8'h58] || data_written < dr_sram[8'h5C])
          alm_out_reg[3] <= 1;
        else
          alm_out_reg[3] <= 0;
      end
      if (chan_out_id_cur == 13) begin //VCC PSINTLP
        if (data_written > dr_sram[8'h59] || data_written < dr_sram[8'h5D])
          alm_out_reg[4] <= 1;
        else
          alm_out_reg[4] <= 0;
        end
        if (chan_out_id_cur == 14) begin // VCC PSINTFP
          if (data_written > dr_sram[8'h5A] || data_written < dr_sram[8'h5E])
            alm_out_reg[5] <= 1;
          else
            alm_out_reg[5] <= 0;
         end
         if (chan_out_id_cur == 15) begin // VCC PSAUX
           if (data_written > dr_sram[8'h5B] || data_written < dr_sram[8'h5F])
             alm_out_reg[6] <= 1;
           else
             alm_out_reg[6] <= 0;
         end
         if (chan_out_id_cur == 32) begin // VUSER 0
           if (data_written > dr_sram[8'h60] || data_written < dr_sram[8'h68])
             alm_out_reg[8] <= 1;
           else
             alm_out_reg[8] <= 0;
         end
      if (chan_out_id_cur == 33) begin // VUSER 1
        if (data_written > dr_sram[8'h61] || data_written < dr_sram[8'h69])
          alm_out_reg[9] <= 1;
        else
          alm_out_reg[9] <= 0;
        end
      if (chan_out_id_cur == 34) begin // VUSER 2
        if (data_written > dr_sram[8'h62] || data_written < dr_sram[8'h6A])
          alm_out_reg[10] <= 1;
        else
          alm_out_reg[10] <= 0;
        end
      if (chan_out_id_cur == 35) begin // VUSER 3
        if (data_written > dr_sram[8'h63] || data_written < dr_sram[8'h6B])
          alm_out_reg[11] <= 1;
        else
          alm_out_reg[11] <= 0;
      end
    end//rst_lock
  end // always 


  always @(*) begin
    ut_fault     = ut_fault_reg & ot_en;
    ut_warn      = ut_warn_reg & alm_en[0];
    alm_ut[11:1] = alm_ut_reg[11:1] & alm_en[11:1];
  end
  
  always @( posedge DCLK_in or posedge sysmon_rst ) begin
    if(sysmon_rst ==1 ) begin
      ut_fault_reg <= 0;
      ut_warn_reg  <= 0;
      alm_ut_reg <= 'd0;
    end
    else if (alm_asrt && avg_final_loop) begin
      case (chan_out_id_cur)
        'd0:  begin //temperature
                ut_fault_reg <= (data_written < dr_sram[8'h57]) ? 1 : 0;
                ut_warn_reg  <= (data_written < dr_sram[8'h54]) ? 1 : 0;
              end
        'd1:  alm_ut_reg[1]  <= (data_written < dr_sram[8'h55]) ? 1 : 0; // VCC INT
        'd2:  alm_ut_reg[2]  <= (data_written < dr_sram[8'h56]) ? 1 : 0; // VCCAUX
        'd6:  alm_ut_reg[3]  <= (data_written < dr_sram[8'h5C]) ? 1 : 0; // VCC BRAM
        'd13: alm_ut_reg[4]  <= (data_written < dr_sram[8'h5D]) ? 1 : 0; // VCC PSINTLP
        'd14: alm_ut_reg[5]  <= (data_written < dr_sram[8'h5E]) ? 1 : 0; // VCC PSINTFP
        'd15: alm_ut_reg[6]  <= (data_written < dr_sram[8'h5F]) ? 1 : 0; // VCC PSAUX
        'd32: alm_ut_reg[8]  <= (data_written < dr_sram[8'h68]) ? 1 : 0; // VUSER 0
        'd33: alm_ut_reg[9]  <= (data_written < dr_sram[8'h69]) ? 1 : 0; // VUSER 1
        'd34: alm_ut_reg[10] <= (data_written < dr_sram[8'h6A]) ? 1 : 0; // VUSER 2
        'd35: alm_ut_reg[11] <= (data_written < dr_sram[8'h6B]) ? 1 : 0; // VUSER 3 
        default: ; //do nothing
      endcase
    end
  end//always

  always @(*) begin
    OT_out = ot_out_reg & ot_en;

    ALM_out[6:0]   = alm_out_reg[6:0] & alm_en[6:0];
    ALM_out[7]     = |ALM_out[6:0];
    ALM_out[11:8]  = alm_out_reg[11:8] & alm_en[11:8];
    ALM_out[14:12] = 'd0; // Reserved
    ALM_out[15]    = (|ALM_out[11:8]) | (|ALM_out[6:0]);
  end

  always @(posedge OT_out) begin
    if(sysmon_rst==0 && ot_limit_reg[3:0]==4'b0011)
      $display("Warning: [Unisim %s-25] OT is high and automatic shutdown in 53h has been enabled. Please refer to the Thermal Management section of the User Guide. Instance: %m", MODULE_NAME, $time/1000.0,);
  end

  // end alarm

  //*** Timing_Checks_Start_here

`ifdef XIL_TIMING
   reg notifier;

   wire dclk_en_n;
   wire dclk_en_p;

   assign dclk_en_n =  IS_DCLK_INVERTED_BIN;
   assign dclk_en_p = ~IS_DCLK_INVERTED_BIN;

   reg notifier_do;

   wire rst_en_n = ~RESET_in && dclk_en_n;
   wire rst_en_p = ~RESET_in && dclk_en_p;

   always @(notifier) begin
      alm_out_reg = 16'bx;
      OT_out = 1'bx;
      BUSY_out = 1'bx;
      EOC_out = 1'bx;
      EOS_out = 1'bx;
      DRDY_out = 1'bx;
      DO_out = 16'bx;
   end 

   always @(notifier_do) begin
      DRDY_out = 1'bx;
      DO_out = 16'bx;
   end


`endif
   
  specify
    (DCLK => ADC_DATA[0]) = (100:100:100, 100:100:100);
    (DCLK => ADC_DATA[10]) = (100:100:100, 100:100:100);
    (DCLK => ADC_DATA[11]) = (100:100:100, 100:100:100);
    (DCLK => ADC_DATA[12]) = (100:100:100, 100:100:100);
    (DCLK => ADC_DATA[13]) = (100:100:100, 100:100:100);
    (DCLK => ADC_DATA[14]) = (100:100:100, 100:100:100);
    (DCLK => ADC_DATA[15]) = (100:100:100, 100:100:100);
    (DCLK => ADC_DATA[1]) = (100:100:100, 100:100:100);
    (DCLK => ADC_DATA[2]) = (100:100:100, 100:100:100);
    (DCLK => ADC_DATA[3]) = (100:100:100, 100:100:100);
    (DCLK => ADC_DATA[4]) = (100:100:100, 100:100:100);
    (DCLK => ADC_DATA[5]) = (100:100:100, 100:100:100);
    (DCLK => ADC_DATA[6]) = (100:100:100, 100:100:100);
    (DCLK => ADC_DATA[7]) = (100:100:100, 100:100:100);
    (DCLK => ADC_DATA[8]) = (100:100:100, 100:100:100);
    (DCLK => ADC_DATA[9]) = (100:100:100, 100:100:100);
    (DCLK => ALM[0]) = (100:100:100, 100:100:100);
    (DCLK => ALM[10]) = (100:100:100, 100:100:100);
    (DCLK => ALM[11]) = (100:100:100, 100:100:100);
    (DCLK => ALM[12]) = (100:100:100, 100:100:100);
    (DCLK => ALM[13]) = (100:100:100, 100:100:100);
    (DCLK => ALM[15]) = (100:100:100, 100:100:100);
    (DCLK => ALM[1]) = (100:100:100, 100:100:100);
    (DCLK => ALM[2]) = (100:100:100, 100:100:100);
    (DCLK => ALM[3]) = (100:100:100, 100:100:100);
    (DCLK => ALM[4]) = (100:100:100, 100:100:100);
    (DCLK => ALM[5]) = (100:100:100, 100:100:100);
    (DCLK => ALM[6]) = (100:100:100, 100:100:100);
    (DCLK => ALM[7]) = (100:100:100, 100:100:100);
    (DCLK => ALM[8]) = (100:100:100, 100:100:100);
    (DCLK => ALM[9]) = (100:100:100, 100:100:100);
    (DCLK => BUSY) = (100:100:100, 100:100:100);
    (DCLK => CHANNEL[0]) = (100:100:100, 100:100:100);
    (DCLK => CHANNEL[1]) = (100:100:100, 100:100:100);
    (DCLK => CHANNEL[2]) = (100:100:100, 100:100:100);
    (DCLK => CHANNEL[3]) = (100:100:100, 100:100:100);
    (DCLK => CHANNEL[4]) = (100:100:100, 100:100:100);
    (DCLK => CHANNEL[5]) = (100:100:100, 100:100:100);
    (DCLK => DO[0]) = (100:100:100, 100:100:100);
    (DCLK => DO[10]) = (100:100:100, 100:100:100);
    (DCLK => DO[11]) = (100:100:100, 100:100:100);
    (DCLK => DO[12]) = (100:100:100, 100:100:100);
    (DCLK => DO[13]) = (100:100:100, 100:100:100);
    (DCLK => DO[14]) = (100:100:100, 100:100:100);
    (DCLK => DO[15]) = (100:100:100, 100:100:100);
    (DCLK => DO[1]) = (100:100:100, 100:100:100);
    (DCLK => DO[2]) = (100:100:100, 100:100:100);
    (DCLK => DO[3]) = (100:100:100, 100:100:100);
    (DCLK => DO[4]) = (100:100:100, 100:100:100);
    (DCLK => DO[5]) = (100:100:100, 100:100:100);
    (DCLK => DO[6]) = (100:100:100, 100:100:100);
    (DCLK => DO[7]) = (100:100:100, 100:100:100);
    (DCLK => DO[8]) = (100:100:100, 100:100:100);
    (DCLK => DO[9]) = (100:100:100, 100:100:100);
    (DCLK => DRDY) = (100:100:100, 100:100:100);
    (DCLK => EOC) = (100:100:100, 100:100:100);
    (DCLK => EOS) = (100:100:100, 100:100:100);
    (DCLK => I2C_SCLK_TS) = (100:100:100, 100:100:100);
    (DCLK => I2C_SDA_TS) = (100:100:100, 100:100:100);
    (DCLK => JTAGBUSY) = (100:100:100, 100:100:100);
    (DCLK => JTAGLOCKED) = (100:100:100, 100:100:100);
    (DCLK => JTAGMODIFIED) = (100:100:100, 100:100:100);
    (DCLK => MUXADDR[0]) = (100:100:100, 100:100:100);
    (DCLK => MUXADDR[1]) = (100:100:100, 100:100:100);
    (DCLK => MUXADDR[2]) = (100:100:100, 100:100:100);
    (DCLK => MUXADDR[3]) = (100:100:100, 100:100:100);
    (DCLK => MUXADDR[4]) = (100:100:100, 100:100:100);
    (DCLK => OT) = (100:100:100, 100:100:100);
    (DCLK => SMBALERT_TS) = (100:100:100, 100:100:100);
    (RESET => BUSY) = (0:0:0, 0:0:0);
    (posedge RESET => (ADC_DATA[0] +: 0)) = (100:100:100, 100:100:100);
    (posedge RESET => (ADC_DATA[10] +: 0)) = (100:100:100, 100:100:100);
    (posedge RESET => (ADC_DATA[11] +: 0)) = (100:100:100, 100:100:100);
    (posedge RESET => (ADC_DATA[12] +: 0)) = (100:100:100, 100:100:100);
    (posedge RESET => (ADC_DATA[13] +: 0)) = (100:100:100, 100:100:100);
    (posedge RESET => (ADC_DATA[14] +: 0)) = (100:100:100, 100:100:100);
    (posedge RESET => (ADC_DATA[15] +: 0)) = (100:100:100, 100:100:100);
    (posedge RESET => (ADC_DATA[1] +: 0)) = (100:100:100, 100:100:100);
    (posedge RESET => (ADC_DATA[2] +: 0)) = (100:100:100, 100:100:100);
    (posedge RESET => (ADC_DATA[3] +: 0)) = (100:100:100, 100:100:100);
    (posedge RESET => (ADC_DATA[4] +: 0)) = (100:100:100, 100:100:100);
    (posedge RESET => (ADC_DATA[5] +: 0)) = (100:100:100, 100:100:100);
    (posedge RESET => (ADC_DATA[6] +: 0)) = (100:100:100, 100:100:100);
    (posedge RESET => (ADC_DATA[7] +: 0)) = (100:100:100, 100:100:100);
    (posedge RESET => (ADC_DATA[8] +: 0)) = (100:100:100, 100:100:100);
    (posedge RESET => (ADC_DATA[9] +: 0)) = (100:100:100, 100:100:100);
    (posedge RESET => (ALM[0] +: 0)) = (100:100:100, 100:100:100);
    (posedge RESET => (ALM[10] +: 0)) = (100:100:100, 100:100:100);
    (posedge RESET => (ALM[11] +: 0)) = (100:100:100, 100:100:100);
    (posedge RESET => (ALM[12] +: 0)) = (100:100:100, 100:100:100);
    (posedge RESET => (ALM[13] +: 0)) = (100:100:100, 100:100:100);
    (posedge RESET => (ALM[15] +: 0)) = (100:100:100, 100:100:100);
    (posedge RESET => (ALM[1] +: 0)) = (100:100:100, 100:100:100);
    (posedge RESET => (ALM[2] +: 0)) = (100:100:100, 100:100:100);
    (posedge RESET => (ALM[3] +: 0)) = (100:100:100, 100:100:100);
    (posedge RESET => (ALM[4] +: 0)) = (100:100:100, 100:100:100);
    (posedge RESET => (ALM[5] +: 0)) = (100:100:100, 100:100:100);
    (posedge RESET => (ALM[6] +: 0)) = (100:100:100, 100:100:100);
    (posedge RESET => (ALM[7] +: 0)) = (100:100:100, 100:100:100);
    (posedge RESET => (ALM[8] +: 0)) = (100:100:100, 100:100:100);
    (posedge RESET => (ALM[9] +: 0)) = (100:100:100, 100:100:100);
    (posedge RESET => (CHANNEL[0] +: 0)) = (100:100:100, 100:100:100);
    (posedge RESET => (CHANNEL[1] +: 0)) = (100:100:100, 100:100:100);
    (posedge RESET => (CHANNEL[2] +: 0)) = (100:100:100, 100:100:100);
    (posedge RESET => (CHANNEL[3] +: 0)) = (100:100:100, 100:100:100);
    (posedge RESET => (CHANNEL[4] +: 0)) = (100:100:100, 100:100:100);
    (posedge RESET => (CHANNEL[5] +: 0)) = (100:100:100, 100:100:100);
    (posedge RESET => (EOC +: 0)) = (100:100:100, 100:100:100);
    (posedge RESET => (EOS +: 0)) = (100:100:100, 100:100:100);
    (posedge RESET => (MUXADDR[0] +: 0)) = (100:100:100, 100:100:100);
    (posedge RESET => (MUXADDR[1] +: 0)) = (100:100:100, 100:100:100);
    (posedge RESET => (MUXADDR[2] +: 0)) = (100:100:100, 100:100:100);
    (posedge RESET => (MUXADDR[3] +: 0)) = (100:100:100, 100:100:100);
    (posedge RESET => (MUXADDR[4] +: 0)) = (100:100:100, 100:100:100);
    (posedge RESET => (OT +: 0)) = (100:100:100, 100:100:100);
  `ifdef XIL_TIMING
    $period (negedge CONVST, 0:0:0, notifier);
    $period (negedge CONVSTCLK, 0:0:0, notifier);
    $period (negedge DCLK, 0:0:0, notifier);
    $period (posedge CONVST, 0:0:0, notifier);
    $period (posedge CONVSTCLK, 0:0:0, notifier);
    $period (posedge DCLK, 0:0:0, notifier);
    $setuphold (negedge DCLK, negedge DADDR[0], 0:0:0, 0:0:0, notifier_do, rst_en_n, rst_en_n, DCLK_delay, DADDR_delay[0]);
    $setuphold (negedge DCLK, negedge DADDR[1], 0:0:0, 0:0:0, notifier_do, rst_en_n, rst_en_n, DCLK_delay, DADDR_delay[1]);
    $setuphold (negedge DCLK, negedge DADDR[2], 0:0:0, 0:0:0, notifier_do, rst_en_n, rst_en_n, DCLK_delay, DADDR_delay[2]);
    $setuphold (negedge DCLK, negedge DADDR[3], 0:0:0, 0:0:0, notifier_do, rst_en_n, rst_en_n, DCLK_delay, DADDR_delay[3]);
    $setuphold (negedge DCLK, negedge DADDR[4], 0:0:0, 0:0:0, notifier_do, rst_en_n, rst_en_n, DCLK_delay, DADDR_delay[4]);
    $setuphold (negedge DCLK, negedge DADDR[5], 0:0:0, 0:0:0, notifier_do, rst_en_n, rst_en_n, DCLK_delay, DADDR_delay[5]);
    $setuphold (negedge DCLK, negedge DADDR[6], 0:0:0, 0:0:0, notifier_do, rst_en_n, rst_en_n, DCLK_delay, DADDR_delay[6]);
    $setuphold (negedge DCLK, negedge DADDR[7], 0:0:0, 0:0:0, notifier_do, rst_en_n, rst_en_n, DCLK_delay, DADDR_delay[7]);
    $setuphold (negedge DCLK, negedge DEN, 0:0:0, 0:0:0, notifier_do, rst_en_n, rst_en_n, DCLK_delay, DEN_delay);
    $setuphold (negedge DCLK, negedge DI[0], 0:0:0, 0:0:0, notifier_do, rst_en_n, rst_en_n, DCLK_delay, DI_delay[0]);
    $setuphold (negedge DCLK, negedge DI[10], 0:0:0, 0:0:0, notifier_do, rst_en_n, rst_en_n, DCLK_delay, DI_delay[10]);
    $setuphold (negedge DCLK, negedge DI[11], 0:0:0, 0:0:0, notifier_do, rst_en_n, rst_en_n, DCLK_delay, DI_delay[11]);
    $setuphold (negedge DCLK, negedge DI[12], 0:0:0, 0:0:0, notifier_do, rst_en_n, rst_en_n, DCLK_delay, DI_delay[12]);
    $setuphold (negedge DCLK, negedge DI[13], 0:0:0, 0:0:0, notifier_do, rst_en_n, rst_en_n, DCLK_delay, DI_delay[13]);
    $setuphold (negedge DCLK, negedge DI[14], 0:0:0, 0:0:0, notifier_do, rst_en_n, rst_en_n, DCLK_delay, DI_delay[14]);   
    $setuphold (negedge DCLK, negedge DI[15], 0:0:0, 0:0:0, notifier_do, rst_en_n, rst_en_n, DCLK_delay, DI_delay[15]);
    $setuphold (negedge DCLK, negedge DI[1], 0:0:0, 0:0:0, notifier_do, rst_en_n, rst_en_n, DCLK_delay, DI_delay[1]);
    $setuphold (negedge DCLK, negedge DI[2], 0:0:0, 0:0:0, notifier_do, rst_en_n, rst_en_n, DCLK_delay,DI_delay[2]);
    $setuphold (negedge DCLK, negedge DI[3], 0:0:0, 0:0:0, notifier_do, rst_en_n, rst_en_n, DCLK_delay,DI_delay[3]);
    $setuphold (negedge DCLK, negedge DI[4], 0:0:0, 0:0:0, notifier_do, rst_en_n, rst_en_n, DCLK_delay, DI_delay[4]);
    $setuphold (negedge DCLK, negedge DI[5], 0:0:0, 0:0:0, notifier_do, rst_en_n, rst_en_n, DCLK_delay, DI_delay[5]);
    $setuphold (negedge DCLK, negedge DI[6], 0:0:0, 0:0:0, notifier_do, rst_en_n, rst_en_n, DCLK_delay, DI_delay[6]);
    $setuphold (negedge DCLK, negedge DI[7], 0:0:0, 0:0:0, notifier_do, rst_en_n, rst_en_n, DCLK_delay, DI_delay[7]);
    $setuphold (negedge DCLK, negedge DI[8], 0:0:0, 0:0:0, notifier_do, rst_en_n, rst_en_n, DCLK_delay, DI_delay[8]);
    $setuphold (negedge DCLK, negedge DI[9], 0:0:0, 0:0:0, notifier_do, rst_en_n, rst_en_n, DCLK_delay, DI_delay[9]);
    $setuphold (negedge DCLK, negedge DWE, 0:0:0, 0:0:0, notifier_do, rst_en_n, rst_en_n, DCLK_delay, DWE_delay);   
    $setuphold (negedge DCLK, posedge DADDR[0], 0:0:0, 0:0:0, notifier_do, rst_en_n, rst_en_n, DCLK_delay, DADDR_delay[0]);
    $setuphold (negedge DCLK, posedge DADDR[1], 0:0:0, 0:0:0, notifier_do, rst_en_n, rst_en_n, DCLK_delay, DADDR_delay[1]);
    $setuphold (negedge DCLK, posedge DADDR[2], 0:0:0, 0:0:0, notifier_do, rst_en_n, rst_en_n, DCLK_delay, DADDR_delay[2]);
    $setuphold (negedge DCLK, posedge DADDR[3], 0:0:0, 0:0:0, notifier_do, rst_en_n, rst_en_n, DCLK_delay, DADDR_delay[3]);
    $setuphold (negedge DCLK, posedge DADDR[4], 0:0:0, 0:0:0, notifier_do, rst_en_n, rst_en_n, DCLK_delay, DADDR_delay[4]);
    $setuphold (negedge DCLK, posedge DADDR[5], 0:0:0, 0:0:0, notifier_do, rst_en_n, rst_en_n, DCLK_delay, DADDR_delay[5]);
    $setuphold (negedge DCLK, posedge DADDR[6], 0:0:0, 0:0:0, notifier_do, rst_en_n, rst_en_n, DCLK_delay, DADDR_delay[6]);
    $setuphold (negedge DCLK, posedge DADDR[7], 0:0:0, 0:0:0, notifier_do, rst_en_n, rst_en_n, DCLK_delay, DADDR_delay[7]);
    $setuphold (negedge DCLK, posedge DEN, 0:0:0, 0:0:0, notifier_do, rst_en_n, rst_en_n, DCLK_delay, DEN_delay);
    $setuphold (negedge DCLK, posedge DI[0], 0:0:0, 0:0:0, notifier_do, rst_en_n, rst_en_n, DCLK_delay, DI_delay[0]);
    $setuphold (negedge DCLK, posedge DI[10], 0:0:0, 0:0:0, notifier_do, rst_en_n, rst_en_n, DCLK_delay, DI_delay[10]);
    $setuphold (negedge DCLK, posedge DI[11], 0:0:0, 0:0:0, notifier_do, rst_en_n, rst_en_n, DCLK_delay, DI_delay[11]);
    $setuphold (negedge DCLK, posedge DI[12], 0:0:0, 0:0:0, notifier_do, rst_en_n, rst_en_n, DCLK_delay, DI_delay[12]);
    $setuphold (negedge DCLK, posedge DI[13], 0:0:0, 0:0:0, notifier_do, rst_en_n, rst_en_n, DCLK_delay, DI_delay[13]);
    $setuphold (negedge DCLK, posedge DI[14], 0:0:0, 0:0:0, notifier_do, rst_en_n, rst_en_n, DCLK_delay, DI_delay[14]);   
    $setuphold (negedge DCLK, posedge DI[15], 0:0:0, 0:0:0, notifier_do, rst_en_n, rst_en_n, DCLK_delay, DI_delay[15]);     
    $setuphold (negedge DCLK, posedge DI[1], 0:0:0, 0:0:0, notifier_do, rst_en_n, rst_en_n, DCLK_delay, DI_delay[1]);
    $setuphold (negedge DCLK, posedge DI[2], 0:0:0, 0:0:0, notifier_do, rst_en_n, rst_en_n, DCLK_delay, DI_delay[2]);
    $setuphold (negedge DCLK, posedge DI[3], 0:0:0, 0:0:0, notifier_do, rst_en_n, rst_en_n, DCLK_delay, DI_delay[3]);
    $setuphold (negedge DCLK, posedge DI[4], 0:0:0, 0:0:0, notifier_do, rst_en_n, rst_en_n, DCLK_delay, DI_delay[4]);
    $setuphold (negedge DCLK, posedge DI[5], 0:0:0, 0:0:0, notifier_do, rst_en_n, rst_en_n, DCLK_delay, DI_delay[5]);
    $setuphold (negedge DCLK, posedge DI[6], 0:0:0, 0:0:0, notifier_do, rst_en_n, rst_en_n, DCLK_delay, DI_delay[6]);
    $setuphold (negedge DCLK, posedge DI[7], 0:0:0, 0:0:0, notifier_do, rst_en_n, rst_en_n, DCLK_delay, DI_delay[7]);
    $setuphold (negedge DCLK, posedge DI[8], 0:0:0, 0:0:0, notifier_do, rst_en_n, rst_en_n, DCLK_delay, DI_delay[8]);
    $setuphold (negedge DCLK, posedge DI[9], 0:0:0, 0:0:0, notifier_do, rst_en_n, rst_en_n, DCLK_delay, DI_delay[9]);
    $setuphold (negedge DCLK, posedge DWE, 0:0:0, 0:0:0, notifier_do, rst_en_n, rst_en_n, DCLK_delay, DWE_delay);
    $setuphold (posedge DCLK, negedge DADDR[0], 0:0:0, 0:0:0, notifier_do, rst_en_p, rst_en_p, DCLK_delay, DADDR_delay[0]);
    $setuphold (posedge DCLK, negedge DADDR[1], 0:0:0, 0:0:0, notifier_do, rst_en_p, rst_en_p, DCLK_delay, DADDR_delay[1]);
    $setuphold (posedge DCLK, negedge DADDR[2], 0:0:0, 0:0:0, notifier_do, rst_en_p, rst_en_p, DCLK_delay, DADDR_delay[2]);
    $setuphold (posedge DCLK, negedge DADDR[3], 0:0:0, 0:0:0, notifier_do, rst_en_p, rst_en_p, DCLK_delay, DADDR_delay[3]);
    $setuphold (posedge DCLK, negedge DADDR[4], 0:0:0, 0:0:0, notifier_do, rst_en_p, rst_en_p, DCLK_delay, DADDR_delay[4]);
    $setuphold (posedge DCLK, negedge DADDR[5], 0:0:0, 0:0:0, notifier_do, rst_en_p, rst_en_p, DCLK_delay, DADDR_delay[5]);
    $setuphold (posedge DCLK, negedge DADDR[6], 0:0:0, 0:0:0, notifier_do, rst_en_p, rst_en_p, DCLK_delay, DADDR_delay[6]);
    $setuphold (posedge DCLK, negedge DADDR[7], 0:0:0, 0:0:0, notifier_do, rst_en_p, rst_en_p, DCLK_delay, DADDR_delay[7]);   
    $setuphold (posedge DCLK, negedge DEN, 0:0:0, 0:0:0, notifier_do, rst_en_p, rst_en_p, DCLK_delay, DEN_delay);
    $setuphold (posedge DCLK, negedge DI[0], 0:0:0, 0:0:0, notifier_do, rst_en_p, rst_en_p, DCLK_delay, DI_delay[0]);
    $setuphold (posedge DCLK, negedge DI[10], 0:0:0, 0:0:0, notifier_do, rst_en_p, rst_en_p, DCLK_delay, DI_delay[10]);
    $setuphold (posedge DCLK, negedge DI[11], 0:0:0, 0:0:0, notifier_do, rst_en_p, rst_en_p, DCLK_delay, DI_delay[11]);
    $setuphold (posedge DCLK, negedge DI[12], 0:0:0, 0:0:0, notifier_do, rst_en_p, rst_en_p, DCLK_delay, DI_delay[12]);
    $setuphold (posedge DCLK, negedge DI[13], 0:0:0, 0:0:0, notifier_do, rst_en_p, rst_en_p, DCLK_delay, DI_delay[13]);
    $setuphold (posedge DCLK, negedge DI[14], 0:0:0, 0:0:0, notifier_do, rst_en_p, rst_en_p, DCLK_delay, DI_delay[14]);   
    $setuphold (posedge DCLK, negedge DI[15], 0:0:0, 0:0:0, notifier_do, rst_en_p, rst_en_p, DCLK_delay, DI_delay[15]);      
    $setuphold (posedge DCLK, negedge DI[1], 0:0:0, 0:0:0, notifier_do, rst_en_p, rst_en_p, DCLK_delay, DI_delay[1]);
    $setuphold (posedge DCLK, negedge DI[2], 0:0:0, 0:0:0, notifier_do, rst_en_p, rst_en_p, DCLK_delay, DI_delay[2]);
    $setuphold (posedge DCLK, negedge DI[3], 0:0:0, 0:0:0, notifier_do, rst_en_p, rst_en_p, DCLK_delay, DI_delay[3]);
    $setuphold (posedge DCLK, negedge DI[4], 0:0:0, 0:0:0, notifier_do, rst_en_p, rst_en_p, DCLK_delay, DI_delay[4]);
    $setuphold (posedge DCLK, negedge DI[5], 0:0:0, 0:0:0, notifier_do, rst_en_p, rst_en_p, DCLK_delay, DI_delay[5]);
    $setuphold (posedge DCLK, negedge DI[6], 0:0:0, 0:0:0, notifier_do, rst_en_p, rst_en_p, DCLK_delay, DI_delay[6]);
    $setuphold (posedge DCLK, negedge DI[7], 0:0:0, 0:0:0, notifier_do, rst_en_p, rst_en_p, DCLK_delay, DI_delay[7]);
    $setuphold (posedge DCLK, negedge DI[8], 0:0:0, 0:0:0, notifier_do, rst_en_p, rst_en_p, DCLK_delay, DI_delay[8]);
    $setuphold (posedge DCLK, negedge DI[9], 0:0:0, 0:0:0, notifier_do, rst_en_p, rst_en_p, DCLK_delay, DI_delay[9]);
    $setuphold (posedge DCLK, negedge DWE, 0:0:0, 0:0:0, notifier_do, rst_en_p, rst_en_p, DCLK_delay, DWE_delay);
    $setuphold (posedge DCLK, posedge DADDR[0], 0:0:0, 0:0:0, notifier_do, rst_en_p, rst_en_p, DCLK_delay, DADDR_delay[0]);
    $setuphold (posedge DCLK, posedge DADDR[1], 0:0:0, 0:0:0, notifier_do, rst_en_p, rst_en_p, DCLK_delay, DADDR_delay[1]);
    $setuphold (posedge DCLK, posedge DADDR[2], 0:0:0, 0:0:0, notifier_do, rst_en_p, rst_en_p, DCLK_delay, DADDR_delay[2]);
    $setuphold (posedge DCLK, posedge DADDR[3], 0:0:0, 0:0:0, notifier_do, rst_en_p, rst_en_p, DCLK_delay, DADDR_delay[3]);
    $setuphold (posedge DCLK, posedge DADDR[4], 0:0:0, 0:0:0, notifier_do, rst_en_p, rst_en_p, DCLK_delay, DADDR_delay[4]);
    $setuphold (posedge DCLK, posedge DADDR[5], 0:0:0, 0:0:0, notifier_do, rst_en_p, rst_en_p, DCLK_delay, DADDR_delay[5]);
    $setuphold (posedge DCLK, posedge DADDR[6], 0:0:0, 0:0:0, notifier_do, rst_en_p, rst_en_p, DCLK_delay, DADDR_delay[6]);
    $setuphold (posedge DCLK, posedge DADDR[7], 0:0:0, 0:0:0, notifier_do, rst_en_p, rst_en_p, DCLK_delay, DADDR_delay[7]);   
    $setuphold (posedge DCLK, posedge DEN, 0:0:0, 0:0:0, notifier_do, rst_en_p, rst_en_p, DCLK_delay, DEN_delay);
    $setuphold (posedge DCLK, posedge DI[0], 0:0:0, 0:0:0, notifier_do, rst_en_p, rst_en_p, DCLK_delay, DI_delay[0]);
    $setuphold (posedge DCLK, posedge DI[10], 0:0:0, 0:0:0, notifier_do, rst_en_p, rst_en_p, DCLK_delay, DI_delay[10]);
    $setuphold (posedge DCLK, posedge DI[11], 0:0:0, 0:0:0, notifier_do, rst_en_p, rst_en_p, DCLK_delay, DI_delay[11]);
    $setuphold (posedge DCLK, posedge DI[12], 0:0:0, 0:0:0, notifier_do, rst_en_p, rst_en_p, DCLK_delay, DI_delay[12]);
    $setuphold (posedge DCLK, posedge DI[13], 0:0:0, 0:0:0, notifier_do, rst_en_p, rst_en_p, DCLK_delay, DI_delay[13]);
    $setuphold (posedge DCLK, posedge DI[14], 0:0:0, 0:0:0, notifier_do, rst_en_p, rst_en_p, DCLK_delay, DI_delay[14]);   
    $setuphold (posedge DCLK, posedge DI[15], 0:0:0, 0:0:0, notifier_do, rst_en_p, rst_en_p, DCLK_delay, DI_delay[15]);      
    $setuphold (posedge DCLK, posedge DI[1], 0:0:0, 0:0:0, notifier_do, rst_en_p, rst_en_p, DCLK_delay, DI_delay[1]);
    $setuphold (posedge DCLK, posedge DI[2], 0:0:0, 0:0:0, notifier_do, rst_en_p, rst_en_p, DCLK_delay, DI_delay[2]);
    $setuphold (posedge DCLK, posedge DI[3], 0:0:0, 0:0:0, notifier_do, rst_en_p, rst_en_p, DCLK_delay, DI_delay[3]);
    $setuphold (posedge DCLK, posedge DI[4], 0:0:0, 0:0:0, notifier_do, rst_en_p, rst_en_p, DCLK_delay, DI_delay[4]);
    $setuphold (posedge DCLK, posedge DI[5], 0:0:0, 0:0:0, notifier_do, rst_en_p, rst_en_p, DCLK_delay, DI_delay[5]);
    $setuphold (posedge DCLK, posedge DI[6], 0:0:0, 0:0:0, notifier_do, rst_en_p, rst_en_p, DCLK_delay, DI_delay[6]);
    $setuphold (posedge DCLK, posedge DI[7], 0:0:0, 0:0:0, notifier_do, rst_en_p, rst_en_p, DCLK_delay, DI_delay[7]);
    $setuphold (posedge DCLK, posedge DI[8], 0:0:0, 0:0:0, notifier_do, rst_en_p, rst_en_p, DCLK_delay, DI_delay[8]);
    $setuphold (posedge DCLK, posedge DI[9], 0:0:0, 0:0:0, notifier_do, rst_en_p, rst_en_p, DCLK_delay, DI_delay[9]);
    $setuphold (posedge DCLK, posedge DWE, 0:0:0, 0:0:0, notifier_do, rst_en_p, rst_en_p, DCLK_delay, DWE_delay);
    $width (negedge CONVST, 0:0:0, 0, notifier);
    $width (negedge CONVSTCLK, 0:0:0, 0, notifier);
    $width (negedge DCLK, 0:0:0, 0, notifier);
    $width (posedge CONVST, 0:0:0, 0, notifier);
    $width (posedge CONVSTCLK, 0:0:0, 0, notifier);
    $width (posedge DCLK, 0:0:0, 0, notifier);
`endif
    specparam PATHPULSE$ = 0;
endspecify


endmodule 

`endcelldefine
