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
//  /   /                        System Monitor
// /___/   /\     Filename    : SYSMONE1.v
// \   \  /  \    
//  \___\/\___\
//
///////////////////////////////////////////////////////////////////////////////
// Revision:
//    01/31/13 - Initial version.
//    03/19/13 - Fixed fatal width problem (CR 707214).
//             - Update MUXADDR width (CR 706758).
//    03/20/13 - Fixed output MSB problem (CR 706163).
//             - Remove SCL and SDA ports (CR 707646). 
//    04/26/13 - Add invertible pin support (PR 683925).
//    05/01/13 - Fixed DRC for IS_*_INVERTED parameters (CR 715818).
//    05/08/13 - Changed Vuser1-4 to Vuser 0-3 (CR 716783).
//    06/04/13 - Added I2CSCLK and I2CSDA ports (CR 721147).
//    06/19/13 - Fixed CHANNEL output (CR 717955).
//    10/15/13 - Added I2C simulation support (CR 707725).
//    10/28/13 - Removed DRC for event mode timing (CR 736315).
//    11/15/13 - Updated I2C support for in and output instead of inout (CR 742395).
//    11/22/13 - Updated VBRAM to VCCBRAM (CR 755165).
//    01/21/14 - Added missing timing (CR 767834).
//    01/21/14 - Fixed Vuser (CR 766501).
//    03/20/14 - Fixed event driven mode in single pass sequence (CR 764936).
//    03/21/14 - Balanced all inputs with xor (CR 778933).
//    04/30/14 - Initialized chan_val and chan_valn (CR 782388).
//    05/27/14 - New simulation library message format.
//    06/17/14 - Fixed default mode sequencer (CR 800173)
//    10/01/14 - Updated conditional timing check for IS_INVERTED parameter.
//    10/22/14 - Added #1 to $finish (CR 808642).
//    12/12/14 - Added missing WIDTH timing check for CONVST (CR 836426).
//               Updated new temperature calculation (CR 828651). 
//    02/04/15 - Fixed DO output with DCLK division 4 or lower (CR 840852).
//    02/19/15 - Fixed I2C initial sync issue (CR 847938).
//    03/06/15 - Fixed I2C addr when I2C_OR = 0 at initial time.
//    03/17/15 - Fixed sequencer out of bound (CR 850975).
//    04/10/15 - Updated new temperature calculation (CR 828651). 
//  End Revision:
///////////////////////////////////////////////////////////////////////////////

`timescale 1ps / 1ps

`celldefine

  module SYSMONE1 #(
`ifdef XIL_TIMING
  parameter LOC = "UNPLACED",
`endif
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
  localparam MODULE_NAME = "SYSMONE1";

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
  `include "SYSMONE1_dr.v"
`else
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
  wire RESET_delay;
`endif

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

  always @(posedge trig_attr) begin
    #1; 
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
    
    if (attr_err == 1'b1) #1 $finish;
       
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

     // CR1004434
     if ((attr_test == 1'b1) ||
        ((INIT_41_BIN[15:12]==4'b0001|| INIT_41_BIN[15:12]==4'b0010) && INIT_46_BIN[3:0]!=4'b0000) ||  //single pass or cont mode and vuser selected
        (INIT_41_BIN[15:12]==4'b0011 && INIT_40_BIN[5:2]==4'b1000) //single channel mode and vuser is selected
        )
           $display("Warning: [Unisim %s-177] INIT_40 and INIT_41 attributes are set to %x and %x respectively. VUSER is selected. In Kintex devices, SYSMONE1 model has no way of knowing whether VUSER has a 6V range or a 3V range and assumes all channels have 3V range. If HR banks are selected, the value stored in the model's registers will be different than that of the actual hardware; and only for this specific case VUSER simulation checks should be ignored. Instance: %m", MODULE_NAME, INIT_40_BIN, INIT_41_BIN);
  end // always @ (trig_dep_attr)

   
  // Total UNISIM %s- warning message next: 59

  localparam CONV_CNT_P            = 37;
  localparam CONV_CNT              = 48; 

  //Convergence periods
  localparam CONV_CAL_PER_RST      = 6;
  localparam CONV_CAL_PER_0        = 2;
  localparam CONV_NOTCAL_PER_1     = 18; //   //minus 3 ->old comment
  localparam CONV_CAL_PER_2        = 96;
  localparam CONV_CAL_PER_3        = 96;
  localparam CONV_CAL_PER_4        = 44;
  localparam CONV_CAL_PER_5        = 21;

  //sequencer operation
  localparam [3:0] SEQ_DEFAULT_MODE   = 4'b0000 ;
  localparam [1:0] SEQ_DEFAULT_MODE2  = 2'b11   ;
  localparam [3:0] SEQ_SINGLE_PASS    = 4'b0001 ;
  localparam [3:0] SEQ_CONT_CHAN      = 4'b0010 ;
  localparam [3:0] SEQ_SINGLE_CHAN    = 4'b0011 ;//means sequencer is off

  //`define    CALIBRATION_ALWAYS_FIRST   

  //adc_state
  localparam  S0_ST = 0,
              S1_ST = 1,
              S2_ST = 2,
              S3_ST = 3,
              S5_ST = 5,
              S6_ST = 6;

  time time_out, prev_time_out;
  
  integer temperature_index = -1, time_index = -1, vccaux_index = -1;
  integer vccbram_index = -1;
  integer vccint_index = -1, vn_index = -1, vp_index = -1;
  integer vccpint_index = -1;
  integer vccpaux_index = -1;
    integer vccpdro_index = -1;
  integer vauxp_idx[15:0]; integer vauxn_idx[15:0];
  integer vuser0_index = -1, vuser1_index = -1;
  integer vuser2_index = -1, vuser3_index = -1;
  integer char_1, char_2, fs, fd;
  integer num_arg, num_val;
  integer clk_count;
  reg     clk_count_rst = 0;
  integer seq_count, seq_count_a;
  integer seq_status_avg, acq_count;
  integer conv_avg_count [63:0];
  wire [7:0] avg_amount;
  integer conv_acc [63:0];
  integer conv_result_int;
  integer conv_count;
  integer h, i, j, k, l, m, n, p;
  integer file_line;

  // string    
  reg [8*12:1] label0, label1, label2, label3, label4, label5, label6, label7, label8, label9, label10, label11, label12, label13, label14, label15, label16, label17, label18, label19, label20, label21, label22, label23, label24, label25, label26, label27, label28, label29, label30, label31, label32, label33, label34, label35, label36, label37, label38, label39, label40, label41, label42, label43, label44, label45, label46;
  reg [8*600:1] one_line;
  reg [8*12:1] label [46:0];
  reg [8*12:1] tmp_label;
  reg end_of_file;
  
  real tmp_va0, tmp_va1, column_real00, column_real100, column_real101;
  real column_real0, column_real1, column_real2, column_real3, column_real4, column_real5, column_real6, column_real7, column_real8, column_real9, column_real10, column_real11, column_real12, column_real13, column_real14, column_real15, column_real16, column_real17, column_real18, column_real19, column_real20, column_real21, column_real22, column_real23, column_real24, column_real25, column_real26, column_real27, column_real28, column_real29, column_real30, column_real31, column_real32, column_real33, column_real34, column_real35, column_real36, column_real37, column_real38, column_real39, column_real40, column_real41, column_real42, column_real43, column_real44, column_real45, column_real46;

  // array of real numbers
  reg [63:0] column_real      [CONV_CNT-1  :0];
  reg [63:0] chan_val         [CONV_CNT_P-1:0];
  reg [63:0] chan_val_tmp     [CONV_CNT_P-1:0];
  reg [63:0] chan_valn        [CONV_CNT_P-1:0];
  reg [63:0] chan_valn_tmp    [CONV_CNT_P-1:0];
  reg [63:0] mn_in_diff       [CONV_CNT_P-1:0];
  reg [63:0] mn_in2_diff      [CONV_CNT_P-1:0];
  reg [63:0] mn_in_uni        [CONV_CNT_P-1:0];
  reg [63:0] mn_in2_uni       [CONV_CNT_P-1:0];
  reg [63:0] mn_comm_in       [CONV_CNT_P-1:0];
  reg [63:0] mn_comm2_in      [CONV_CNT_P-1:0];

  real chan_val_p_tmp, chan_val_n_tmp;
  real mn_mux_in, mn_in_tmp, mn_comm_in_tmp, mn_in_comm;
  real tmp_v, tmp_v1;
  real adc_temp_result, adc_intpwr_result;
  real adc_ext_result;

  reg seq_reset, seq_reset_dly, seq_reset_flag, seq_reset_flag_dly;
  reg soft_reset = 0;
  reg en_data_flag;
  reg first_cal_chan;
  reg seq_en;
  reg seq_en_dly;
  wire [15:0] flag_reg0, flag_reg1;
  reg [15:0] ot_limit_reg = 16'hCA30;
  reg [15:0] tmp_otv;
  reg [23:0] conv_acc_vec;
  reg [15:0] conv_result;
  reg [15:0] conv_result_reg, conv_acc_result;
  wire [7:0] curr_clkdiv_sel;
  reg [15:0]  alm_out_reg;
  reg [5:0] curr_chan, curr_chan_lat;
  reg [15:0] data_written;
  reg [2:0] adc_state, adc_next_state;
  reg conv_start, conv_end;
  reg eos_en, eos_tmp_en;
  reg DRDY_out_tmp1, DRDY_out_tmp2, DRDY_out_tmp3;
  reg ot_out_reg;
  reg  [15:0] DO_out_rdtmp;
  reg  [15:0] data_reg [63:0];
  reg  [15:0] dr_sram [255:64];
  reg sysclk;
  reg adcclk_tmp;
  wire adcclk;
  wire sysmone1_en, sysmone12_en;
  reg [3:0] curr_seq1_0;
  reg [3:0] curr_seq1_0_lat;
  reg curr_e_c, curr_b_u, curr_acq;
  reg seq_count_en;
  reg [5:0]   acq_chan;
  reg [4:0]   acq_chan_m;
  
  wire        ext_mux_en;
  wire [5:0]  ext_mux_chan;
  wire        default_mode;
  wire        single_pass_mode;
  wire        cont_seq_mode;
  wire        single_chan_mode;
  reg         acq_b_u;
  reg         single_pass_finished; 
  reg         acq_acqsel;
  wire acq_e_c;
  reg acq_e_c_tmp5, acq_e_c_tmp6;
  reg [1:0] averaging, averaging_d;
  reg eoc_en, eoc_en_delay;
  reg EOC_out_tmp, EOS_out_tmp;
  reg EOC_out_tmp1, EOS_out_tmp1;
  reg EOC_out_pre;
  reg EOC_out_pre2;
  reg busy_r, busy_r_rst;
  reg busy_sync1, busy_sync2;
  wire busy_sync_fall, busy_sync_rise;
  reg rst_lock, rst_lock_early, rst_lock_late;
  reg sim_file_flag;
  reg [7:0] DADDR_in_lat;
  reg [15:0] curr_seq,  curr_seq_m;
  reg busy_rst, busy_conv, busy_seq_rst;
  wire [3:0] seq1_0;
  reg  [3:0] seq_bits;
  reg ot_en, alm_update, drp_update, cal_chan_update;
  reg [13:0] alm_en;
  reg [4:0] scon_tmp;
  wire [15:0] seq_chan_reg1, seq_chan_reg2, seq_chan_reg3;
  wire [15:0] seq_acq_reg1, seq_acq_reg2, seq_acq_reg3;
  wire [15:0] seq_avg_reg1, seq_avg_reg2, seq_avg_reg3;
  wire [15:0] seq_bu_reg1, seq_bu_reg2, seq_bu_reg3;
  reg [15:0] cfg_reg1_init;
 
  reg [5:0] seq_curr_i, seq_curr_ia;
  integer busy_rst_cnt;
  integer     si; 
  integer     hr_tot_chan;
  integer       seq_mem [37:0];

  wire rst_in, adc_convst;
  wire [15:0] cfg_reg0;
  wire [15:0] cfg_reg1;
  wire [15:0] cfg_reg2;
  wire [15:0] cfg_reg3;
  reg  reserved_addr_pre;
  reg  read_only_pre;
  reg  RESERVED_ADDR;
  reg  READ_ONLY;
  wire i2c_addr_cap = 0;
  wire i2c_addr_cap_ne;
  reg  i2c_addr_cap_d;
  wire convst_in_pre;
  reg  CONVST_reg;
  wire rst_in_not_seq;
  wire adcclk_div1;
  wire gsr_in;
  assign JTAGBUSY_out     = 0;
  assign JTAGLOCKED_out   = 0;
  assign JTAGMODIFIED_out = 0;
  assign gsr_in         = glblGSR;

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

  //CR 675227 
  //for single pass mode

  integer halt_adc = 0;
  reg int_rst;
  reg int_rst_halt_adc = 0;
  
  always @(posedge RESET_in)
    halt_adc <= 0;

  always @(seq1_0) begin
    if (halt_adc == 2 && single_pass_mode) begin
      halt_adc <= 0;
      int_rst_halt_adc <= 1;
      @(posedge DCLK_in)
      int_rst_halt_adc <= 0;
    end
    
  end
    
  real        i2c_vpvn_addr_tmp;
  integer     i2c_conv_result_int;
  reg         i2c_en;
  reg         i2c_oride;
  reg  [6:0]  i2c_device_addr;
  reg  [6:0]  i2c_device_addr_vpvn;
  reg  [15:0] conv_result_i2c_addr;
  
  initial begin
    i2c_en              = 1;
  end

  // I2C slave address mapping
  always @(*) begin
    i2c_en          = cfg_reg3[7];
    i2c_oride       = cfg_reg3[15];
    i2c_device_addr = (i2c_oride) ? cfg_reg3[14:8]: i2c_device_addr_vpvn;
  end


  assign convst_in_pre  = (CONVST_in===1 || CONVSTCLK_in===1) ? 1: 0;
  
  always @(posedge convst_in_pre or negedge convst_in_pre or posedge rst_in)
    if (rst_in == 1 || rst_lock == 1)
      CONVST_reg <= 0;
    else if (convst_in_pre == 1)
      CONVST_reg <= 1;
    else if (convst_in_pre == 0)
      CONVST_reg <= 0;


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

    tmp_otv = INIT_53_BIN;
    if (tmp_otv [3:0] == 4'b0011) begin
      dr_sram[8'h53] = INIT_53_BIN;
      ot_limit_reg  = INIT_53_BIN;
    end
    else begin
      dr_sram[8'h53] = 16'hCA30;
      ot_limit_reg  = 16'hCA30;
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
                "VCCPINT" : vccpint_index = m;
                "VCCPAUX" : vccpaux_index = m;
                "VCCDDRO" : vccpdro_index = m;
                "VN"            : vn_index = m;
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
                "VP"            : vp_index = m;
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
                default         : begin
                                    $display("Error: [Unisim %s-5] The channel name %s is invalid in the input file. Instance: %m", MODULE_NAME, tmp_label);
                                    infile_format;
                                  end
              endcase
            end // for (m = 0; m < num_arg; m = m +1)


          end // Getting labels
          
          // Getting column values
          else if (char_1 == "0" | char_1 == "1" | char_1 == "2" | char_1 == "3" | char_1 == "4" | char_1 == "5" | char_1 == "6" | char_1 == "7" | char_1 == "8" | char_1 == "9") begin
        
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
            chan_val[13] = column_real[vccpint_index];
            chan_val[14] = column_real[vccpaux_index];
            chan_val[15] = column_real[vccpdro_index];
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
    $display("\n***** SYSMONE1 Simulation analog Data File Format *****\n");
    $display("NAME: design.txt or user file name passed with parameter/generic SIM_MONITOR_FILE\n");
    $display("FORMAT: First line is header line. Valid column name are: TIME TEMP VCCINT VCCAUX VCCBRAM VCCPINT VCCPAUX VCCDDRO VP VN VAUXP[0] VAUXN[0] ..... \n");
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

  // Check if (Vp+Vn)/2 = 0.5 +/- 100 mv,  unipolar only
  always @( posedge busy_r ) begin
    if (acq_b_u == 0 && rst_in == 0 && ((acq_chan == 3) || (acq_chan >= 16 && acq_chan <= 31))) begin  
      chan_val_p_tmp = $bitstoreal(chan_val_tmp[acq_chan]);
      chan_val_n_tmp = $bitstoreal(chan_valn_tmp[acq_chan]);

      if ( chan_val_n_tmp > chan_val_p_tmp)
        $display("Warning: [Unisim %s-8] The N input for external channel %x must be smaller than P input when in unipolar mode (P=%0.2f N=%0.2f) at %.3f ns. Instance: %m", MODULE_NAME, acq_chan, chan_val_p_tmp, chan_val_n_tmp, $time/1000.0);
      if ( chan_val_n_tmp > 0.5 || chan_val_n_tmp < 0.0)
        $display("Warning: [Unisim %s-9] The range of N input for external channel %x should be between 0V to 0.5V when in unipolar mode (N=%0.2f) at %.3f ns. Instance: %m", MODULE_NAME, acq_chan, chan_val_n_tmp, $time/1000.0);
    end
  end

  reg seq_reset_busy_out = 0;
  wire rst_in_out;

  always @(posedge DCLK_in or posedge rst_in_out) begin
    if (rst_in_out) begin
      busy_rst <= 1;
      rst_lock <= 1;
      rst_lock_early <= 1;
      rst_lock_late <= 1;
      busy_rst_cnt <= 0;
    end
    else begin
      if (rst_lock == 1) begin
        if (busy_rst_cnt < 29) begin
          busy_rst_cnt <= busy_rst_cnt + 1;
        if ( busy_rst_cnt == 26)
          rst_lock_early <= 0;
        end
        else begin
          busy_rst <= 0;
          rst_lock = 0;
        end
      end
      if (BUSY_out == 0)
        rst_lock_late <= 0;
      end
    end

  initial begin
    BUSY_out = 0;
    busy_rst = 0;
    busy_conv = 0;
    busy_seq_rst = 0;
  end 

  always @(busy_rst or busy_conv or rst_lock) begin
    if (rst_lock)
      BUSY_out = busy_rst;
    else
      BUSY_out = busy_conv;
  end

  always @(posedge DCLK_in or posedge rst_in) begin
    if (rst_in) begin
      busy_conv <= 0;
    end
    else begin
      if (seq_reset_flag == 1 && curr_clkdiv_sel <= 8'h03)
        busy_conv <= busy_seq_rst;
      else if (busy_sync_fall)
        busy_conv <= 0;
      else if (busy_sync_rise)
        busy_conv <= 1;
    end
  end

  always @(posedge DCLK_in or posedge rst_in) begin
    if (rst_in)
      cal_chan_update <= 0;
    else begin
      if (conv_count == CONV_CAL_PER_5 && curr_chan == 6'd8)
        cal_chan_update  <= 1;
      else
        cal_chan_update  <= 0;
    end
  end

  //always @(posedge adcclk or rst_lock)
  always @(posedge DCLK_in or rst_lock) begin
    if (rst_lock) begin
      busy_sync1 <= 0;
      busy_sync2 <= 0;
    end
    else begin
      busy_sync1 <= busy_r;
      busy_sync2 <= busy_sync1;
    end 
  end

  assign busy_sync_fall = (busy_r == 0 && busy_sync1 == 1) ? 1 : 0;
  assign busy_sync_rise = (busy_sync1 == 1 && busy_sync2 == 0 ) ? 1 : 0;

  always @(negedge BUSY_out or posedge busy_r)
    if (seq_reset_flag == 1 && default_mode && curr_clkdiv_sel <= 8'h03) begin
      repeat (5) @(posedge DCLK_in);
      busy_seq_rst <= 1;
    end
    else if (seq_reset_flag == 1 && !default_mode  && curr_clkdiv_sel <= 8'h03) begin
      repeat (7) @(posedge DCLK_in);
      busy_seq_rst <= 1;
    end
    else
      busy_seq_rst <= 0;

  //assign muxaddr_o = (rst_lock_early) ? 5'b0 : (curr_seq1_0_lat[3:2] != 2'b10 && sysmone12_en == 0 || sysmone12_en == 1) ?  acq_chan_m : 5'b0;

  always @(posedge adcclk or posedge RESET_in ) begin
    if (RESET_in) 
      MUXADDR_out <= 5'b0;
    else begin
      if(ext_mux_en &&(curr_seq1_0_lat[3:2] != 2'b10 && sysmone12_en == 0 || sysmone12_en == 1))
        MUXADDR_out <= acq_chan_m;
      else
        MUXADDR_out <= 5'b0;
    end
  end

  always @(negedge BUSY_out or posedge BUSY_out or posedge rst_in_out or posedge cal_chan_update )
    if (rst_in_out || rst_lock_late)
      CHANNEL_out <= 5'd0;
    else if (BUSY_out ==1 && (cal_chan_update == 1) )
      CHANNEL_out <= 6'd8;
    else if (BUSY_out == 0) begin
       if ((curr_seq1_0_lat[3:2] != 2'b10 && sysmone12_en == 0) || sysmone12_en == 1)
      CHANNEL_out <= curr_chan;
       else
         CHANNEL_out <= 5'b0;
      curr_chan_lat <= curr_chan;
      averaging_d <= averaging;
    end


  // START double latch rst_in
    
  reg rst_in1_tmp6;
  reg rst_in2_tmp6;
  wire RESET_in_t;
  wire rst_in2;

  initial begin
    int_rst = 1;
    repeat (2) @(posedge DCLK_in);
    int_rst <= 0;
  end

  initial begin
    rst_in1_tmp6 = 0;
    rst_in2_tmp6 = 0;
  end

  assign #1 RESET_in_t = int_rst_halt_adc | RESET_in | int_rst | soft_reset | gsr_in;

    
  always@(posedge adcclk or posedge RESET_in_t)
    if (RESET_in_t) begin
      rst_in2_tmp6 <= 1;
      rst_in1_tmp6 <= 1;
    end
    else begin
      rst_in2_tmp6 <= rst_in1_tmp6;
      rst_in1_tmp6 <= RESET_in_t;
    end

  assign rst_in2 =  rst_in2_tmp6;
  assign #10 rst_in_not_seq = rst_in2;
  assign rst_in = rst_in_not_seq | seq_reset_dly;
  assign rst_in_out = rst_in_not_seq | seq_reset_busy_out;
 
  always @(posedge seq_reset) begin
    repeat (2) @(posedge DCLK_in);
    seq_reset_dly = 1;
    repeat (2) @(negedge DCLK_in);
    seq_reset_busy_out = 1;
    repeat (3) @(posedge DCLK_in);
    seq_reset_dly = 0;
    seq_reset_busy_out = 0;
  end
      
  always @(posedge seq_reset_dly or posedge busy_r)
    if (seq_reset_dly)
      seq_reset_flag <= 1;
    else
      seq_reset_flag <= 0; 

  always @(posedge seq_reset_flag or posedge BUSY_out)
    if (seq_reset_flag)
      seq_reset_flag_dly <= 1;
    else  //if(!CHANNEL_out==6'd8) 
      seq_reset_flag_dly <= 0;

  always @(posedge BUSY_out )
    if (seq_reset_flag_dly == 1 && acq_chan == 6'd8 && default_mode )
      first_cal_chan <= 1;
    else
      first_cal_chan <= 0;
       


  initial begin
    sysclk = 0;
    adcclk_tmp = 0;
       seq_count = 1;
       seq_count_a = 1;
    eos_en          = 0;
    eos_tmp_en      = 0;
    clk_count = -1;
    acq_acqsel = 0;
    acq_e_c_tmp6 = 0;
    acq_e_c_tmp5 = 0;
    eoc_en = 0;
    eoc_en_delay = 0;
    rst_lock = 0;
    rst_lock_early = 0;
    alm_update = 0;
    drp_update = 0;
    cal_chan_update = 0;
    adc_state = S3_ST;
    scon_tmp = 0;
    busy_r = 0;
    busy_r_rst = 0;
    busy_sync1 = 0;
    busy_sync2 = 0;
    conv_count = 0;
    conv_end = 0;
    seq_status_avg = 0;
    for (i = 0; i <=63; i = i +1) begin
      conv_avg_count[i] = 0;   
      conv_acc[i] = 0;
    end
    single_pass_finished = 0;
       for (k = 0; k <= 31; k = k + 1) begin
          data_reg[k] = 16'b0;
       end 
    seq_count_en = 0;
    EOS_out_tmp = 0;
    EOC_out_tmp = 0;
    EOS_out_tmp1 = 0;
    EOC_out_tmp1 = 0;
    EOS_out = 0;
    EOC_out = 0;
    EOC_out_pre = 0;
    EOC_out_pre2 = 0;
    averaging = 0;
    averaging_d = 0;
    curr_e_c = 0;
    curr_b_u = 0;
    curr_acq = 0;
    curr_seq1_0 = 0;
    curr_seq1_0_lat = 0;
    DADDR_in_lat = 0;
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
      curr_chan  = 'd0;
      acq_chan   = 'd0;
      acq_chan_m = 'd0;
      curr_chan_lat =  'd0;
    BUSY_out = 0;
    curr_seq = 0;
    curr_seq_m = 0;
    hr_tot_chan = 0;
    seq_reset_flag_dly = 0;
    seq_reset_flag = 0;
    seq_reset_dly = 0;
    ot_en = 1;
    alm_en = 13'h1FFF;
    DO_out_rdtmp = 0;
    acq_b_u = 0;
    conv_result_int = 0;
    conv_result = 0;
    conv_result_reg = 0;
    reserved_addr_pre = 0;
  end


  // state machine
  always @(posedge adcclk or posedge rst_in or sim_file_flag) begin
    //CR 675227
    if (!(halt_adc == 2 && single_chan_mode )) begin
      if (sim_file_flag == 1'b1)
        adc_state <= S0_ST; 
      else if (rst_in == 1'b1 || rst_lock_early == 1)
        adc_state <= S0_ST;
      else if (rst_in == 1'b0)
        adc_state <= adc_next_state;
    end
  end
    
  always @(adc_state or eos_en or conv_start or conv_end or curr_seq1_0_lat) begin
    case (adc_state)
      S0_ST : adc_next_state = S2_ST;

      S2_ST : if (conv_start)
                adc_next_state = S3_ST;
              else
                adc_next_state = S2_ST;

      S3_ST : if (conv_end)
                  adc_next_state = S5_ST;
                else
              adc_next_state = S3_ST;

      S5_ST : if (curr_seq1_0_lat == SEQ_SINGLE_PASS ) begin
                //CR 675227         if (eos_en)
                if (eos_tmp_en)
                  adc_next_state = S1_ST;
                else
                  adc_next_state = S2_ST;
              end
              else
                adc_next_state = S2_ST;
                
      S1_ST : adc_next_state = S0_ST;

      default : 
              adc_next_state = S0_ST;

    endcase // case(adc_state)

    end 
    
// end state machine    
    

// DRPORT - SRAM
  initial begin
    DRDY_out = 0;
    DRDY_out_tmp1 = 0;
    DRDY_out_tmp2 = 0;
    DRDY_out_tmp3 = 0;
    en_data_flag = 0;
    DO_out = 16'b0;
    seq_reset = 0;
    cfg_reg1_init = INIT_41_BIN;
    seq_en = 0; 
    seq_en_dly = 0;
    seq_en <= #20 (cfg_reg1_init[15:12] != 4'b0011 ) ? 1 : 0;
    seq_en <= #150 0;
  end

  always @(posedge DRDY_out_tmp3 or posedge gsr_in) begin
    if (gsr_in == 1) 
      DRDY_out <= 0;
    else begin
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

    is_reserved_address_pre = ((address_in >= 8'h07 && address_in <= 8'h0F) ||
                               (address_in >= 8'h28 && address_in <= 8'h37) ||
                               (address_in >= 8'h39 && address_in <= 8'h3D) ||
                               (address_in >= 8'h44 && address_in <= 8'h45) ||
                               (address_in >= 8'h58 && address_in <= 8'h5F) ||
                               (address_in >= 8'h64 && address_in <= 8'h67) ||
                               (address_in >= 8'h6C && address_in <= 8'h7F) || 
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

    is_readonly_address_pre = ((address_in <= 8'h3F) ||
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
    end
    else  begin
      if (DEN_in == 1'b1) begin
        if (DRDY_out_tmp1 == 1'b0) begin
          DRDY_out_tmp1     <= 1'b1;
          en_data_flag      = 1;
          DADDR_in_lat      <= DADDR_in;
        end
        else if (DADDR_in != DADDR_in_lat)
          $display("Warning: [Unisim %s-10] Input pin DEN at time %.3f ns can not be continuously set to high. Please wait for DRDY to be high and then set DEN to high again. Instance: %m", MODULE_NAME, $time/1000.0);  
      end // if (DEN_in == 1'b1)
      else
        DRDY_out_tmp1 <= 1'b0;

      DRDY_out_tmp2 <= DRDY_out_tmp1;
      DRDY_out_tmp3 <= DRDY_out_tmp2;

      if (DRDY_out_tmp1 == 1)
        en_data_flag = 0;

      if (DRDY_out_tmp3 == 1) begin
          DO_out            <= DO_out_rdtmp;
      end

      if (DEN_in == 1 && is_reserved_address(DADDR_in) )
        reserved_addr_pre <= 1;
      else if (DWE_in == 1'b1 && DEN_in == 1'b1 && en_data_flag == 1) begin
        //write to all available and writable addresses.
        dr_sram[DADDR_in] <= DI_in;
        //check write access
        if (is_readonly_address(DADDR_in))
          read_only_pre <= 1;
        else begin
          read_only_pre <= 0;

          // post processing after DRP write
          if (DADDR_in == 8'h03)
            soft_reset <= 1;
          else if ( DADDR_in == 8'h53 && DI_in[3:0] == 4'b0011)
              ot_limit_reg[15:4] <= DI_in[15:4];
          else if (DADDR_in == 8'h41  ) begin // && en_data_flag == 1) begin is above
            //if (DEN_in == 1'b1 && DWE_in == 1'b1) begin
            if (DI_in[15:12] != cfg_reg1[15:12])  // writing with the same seq[3:0] will not restart the sequence, matching with hw
              seq_reset <= 1'b1;
            else
              seq_reset <= 1'b0;

            if (DI_in[15:12] != SEQ_SINGLE_CHAN)
              seq_en <= 1'b1;
            else
              seq_en <= 1'b0;
          end //DADDR_in == 8'h41 
        end // not read only
      end // dwe ==1          

      if (seq_en == 1) 
          seq_en <= 1'b0;
      if (seq_reset == 1)
          seq_reset <= 1'b0;
      if (soft_reset == 1)
          soft_reset <= 0;

    end // if (gsr == 1)
  end //always

  reg display_configuration_warnings; 
  reg [7:0] cfg_check_addr;
  always @(posedge DCLK_in or posedge rst_in) begin
    if(rst_in) begin
      display_configuration_warnings <= 0;
      cfg_check_addr                 <= 0;
    end
    else begin
      if(DEN_in && DWE_in) begin 
        display_configuration_warnings <= 1;
        cfg_check_addr                 <= DADDR_in;
      end
      else begin
        display_configuration_warnings <= 0;
        cfg_check_addr                 <= 0;
      end
    end
  end

  always @(posedge display_configuration_warnings) begin
    if(cfg_check_addr == 8'h40) 
      if (cfg_reg0[5:0] == 6'd7 || (cfg_reg0[5:0] >= 6'd9 && cfg_reg0[5:0] <= 6'd12) || cfg_reg0[5:0] >= 6'd36)
        $display("Warning: [Unisim %s-14] Config register 0 bits [5:0] at 40h cannot not be set to an invalid analog channel value as %0b. Instance: %m", MODULE_NAME, cfg_reg0[5:0], $time/1000.0,);
    if(cfg_check_addr == 8'h40 || cfg_check_addr==8'h41) 
      if ((cfg_reg1[15:12]==SEQ_SINGLE_CHAN) && (cfg_reg0[8]==1) && (cfg_reg0[5:0] != 6'd3) && (cfg_reg0[5:0] < 6'd16))
        $display("Warning: [Unisim %s-15] In single channel mode if the selected channel is not analog, config register 0 bit[8] must be set to 0. Long acqusition mode is only allowed for external channels, not in single channel mode. Instance: %m", MODULE_NAME, DI_in, DADDR_in, $time/1000.0);
    if(cfg_check_addr == 8'h40 || cfg_check_addr==8'h41|| cfg_check_addr==8'h46|| cfg_check_addr==8'h48|| cfg_check_addr==8'h49) 
      if ((cfg_reg1[15:12]==SEQ_SINGLE_CHAN) && (cfg_reg0[13:12]!=2'b00) && (seq_chan_reg1 != 16'h0000) && (seq_chan_reg2 != 16'h0000) && (seq_chan_reg3 != 16'h0000))
        $display("Warning: [Unisim %s-16] In single channel mode, ADC channel selection registers 46h, 48h and 49h must be set to 0, these are set to %x, %x and %x respectively. Averaging must be enabled. Instance: %m", MODULE_NAME, seq_chan_reg3, seq_chan_reg1, seq_chan_reg2, $time/1000.0);
    if(cfg_check_addr == 8'h4E || cfg_check_addr==8'h41) 
      if ((cfg_reg1[15:12]!=SEQ_SINGLE_CHAN) && ((dr_sram['h4E][10:0]!=11'd0) || (dr_sram['h4E][15:12]!=4'd0)))
        $display("Warning: [Unisim %s-18] The Control Register 4Eh value set is to %x.  Bits [15:12] and [10:0] of this register must be set to 0. Long acquistion mode is only allowed for external channels. Instance: %m", MODULE_NAME, dr_sram['h4E], $time/1000.0);
    if(cfg_check_addr == 8'h42) 
      if (cfg_reg2[4]==1) 
        $display("Warning: [Unisim %s-12] The config reg 2 =%x is invalid. Bit [4] must be set to 0. Instance: %m", MODULE_NAME, cfg_reg2, $time/1000.0);
    if(cfg_check_addr == 8'h43) 
      if (cfg_reg3[3:0]!=4'd0) 
        $display("Warning: [Unisim %s-17] The config reg 3 =%x is invalid. Bits [3:0] must be set to 000. Instance: %m", MODULE_NAME, cfg_reg3, $time/1000.0);
    // CR1004434
    if (cfg_check_addr == 8'h40 || cfg_check_addr ==8'h41) 
      if (((cfg_reg1[15:12]==4'b0001|| cfg_reg1[15:12]==4'b0010) && dr_sram['h46][3:0]!=4'b0000) ||  //single pass or cont mode and vuser selected
          (cfg_reg1[15:12]==4'b0011 && cfg_reg0[5:2]==4'b1000) ) //single channel mode and vuser is selected
        $display("Warning: [Unisim %s-178] The control registers 40h and 41h are set to %x and %x respectively. VUSER is selected. In Kintex devices, SYSMONE1 model has no way of knowing whether VUSER has a 6V range or a 3V range and assumes all channels have 3V range. If 6V banks are selected, the value stored in the model's registers will be different than that of the actual hardware. Instance: %m", 
          MODULE_NAME, cfg_reg0, cfg_reg1 );
  end


    // DO bus data out

   assign flag_reg0 = {8'b0,  ALM_out[6:3], OT_out, ALM_out[2:0]};
   assign flag_reg1 = {10'b0, ALM_out[13:8]};

  always @(*) begin
    reserved_addr_pre = is_reserved_address(DADDR_in_lat);
    if(reserved_addr_pre)
      DO_out_rdtmp      = 16'b0;
    else begin //readable addresses
      if ( DADDR_in_lat <= 8'h3D)
        DO_out_rdtmp = data_reg[DADDR_in_lat];
      else if (DADDR_in_lat == 8'h3E)
        DO_out_rdtmp = flag_reg1;
      else if (DADDR_in_lat == 8'h3F)
        DO_out_rdtmp = flag_reg0;
      else
        DO_out_rdtmp = dr_sram[DADDR_in_lat];
    end
  end

// end DRP RAM

    
  assign cfg_reg0 = dr_sram[8'h40];
  assign cfg_reg1 = dr_sram[8'h41];
  assign cfg_reg2 = dr_sram[8'h42];
  assign cfg_reg3 = dr_sram[8'h43];
  assign seq_chan_reg1 = dr_sram[8'h48];
  assign seq_chan_reg2 = dr_sram[8'h49];
  assign seq_chan_reg3 = dr_sram[8'h46];
  assign seq_avg_reg1 = dr_sram[8'h4A];
  assign seq_avg_reg2 = dr_sram[8'h4B];
  assign seq_avg_reg3 = dr_sram[8'h47];
  assign seq_bu_reg1 = dr_sram[8'h4C];
  assign seq_bu_reg2 = dr_sram[8'h4D];
  assign seq_bu_reg3 = dr_sram[8'h78];
  assign seq_acq_reg1 = dr_sram[8'h4E];
  assign seq_acq_reg2 = dr_sram[8'h4F];
  assign seq_acq_reg3 = dr_sram[8'h79];
 

  assign seq1_0           = cfg_reg1[15:12];
  assign default_mode     = (seq1_0 == 4'b0000 || seq1_0[3:2] == 2'b11);
  assign single_pass_mode = (seq1_0 == 4'b0001);
  assign cont_seq_mode    = (seq1_0 == 4'b0010);
  assign single_chan_mode = (seq1_0 == 4'b0011);
  assign ext_mux_chan     = cfg_reg0[5:0];
  assign ext_mux_en       = cfg_reg0[11]; // && (~default_mode) ??

  always @(posedge drp_update or posedge rst_in) begin
    if (rst_in) begin
      repeat (2)  @(posedge DCLK_in);
      seq_bits = seq1_0;
    end
    else begin
      seq_bits = curr_seq1_0;
      if (seq_bits == SEQ_DEFAULT_MODE) begin
        alm_en  <= 'd0;
        ot_en     <= 1;
      end
      else begin
        ot_en          <= ~cfg_reg1[0];
        alm_en[2:0]  <= ~cfg_reg1[3:1];
        alm_en[6:3]  <= ~cfg_reg1[11:8];
        alm_en[11:8] <= ~cfg_reg3[3:0]; //TODO check this with UG
      end
    end
  end

  //--------------------- end DRPORT - sram    

  //---- I2C logic start ----------------------------------------------------
  parameter  ST_I2C_IDLE      = 2'd0,
             ST_I2C_GET_ADDR  = 2'd1,
             ST_I2C_GET_CMD   = 2'd2,
             ST_I2C_READ      = 2'd3;

  localparam I2C_DRP_RD = 4'b0001; // read 
  localparam I2C_DRP_WR = 4'b0010; // write
  localparam I2C_DRP_NO = 4'b0000; // no operation
  

   
  reg  [1:0]  i2c_state;
  reg         i2c_start;
  reg         i2c_start_reset;
  reg         i2c_stop;
  reg         i2c_stop_reset;
  reg  [3:0]  i2c_bit_counter;
  reg  [2:0]  i2c_byte_counter;
  wire        i2c_lsb_bit;
  wire        i2c_ack_bit;
  wire [15:0] i2c_drp_data;
  wire [9:0]  i2c_drp_addr;
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
  wire        i2c_wr_exec;

  assign i2c_addr_match     = (i2c_data_in[7:1]==i2c_device_addr[6:0]) ? 1 : 0;
  assign i2c_addr_match_wop = i2c_addr_match;


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
  assign i2c_rd_cmd_pre = i2c_rw_bit && I2C_SDA_in; 
   
  always @(posedge RESET_in or posedge i2c_stop or negedge I2C_SCLK_in) begin
    if(RESET_in || i2c_stop)
      i2c_rd_cmd <= 1'b0;
    else begin
      if (i2c_state==ST_I2C_IDLE)
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
    else if ((i2c_state==ST_I2C_IDLE) || i2c_bit_counter=='d1)
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
    else if(i2c_ack_bit && (i2c_state == ST_I2C_GET_CMD || i2c_state == ST_I2C_READ ))
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
                            if(!i2c_addr_match) begin
                              i2c_state <= ST_I2C_IDLE;
                              $display("Warning: [Unisim %s-54] I2C command address h%0X not matching the device address h%0X @time %0t", 
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

  always @(negedge I2C_SCLK_in) begin
    if(!RESET_in) begin
      if(i2c_cmd_received && i2c_drp_cmd==I2C_DRP_WR)
        if(i2c_drp_addr>='h40)
          dr_sram[i2c_drp_addr] <= i2c_drp_data;
        //else
        //  data_reg[i2c_drp_addr] <= i2c_drp_data;
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

  //Pull down SDA to transfer a zero to the master.
  always@(posedge RESET_in or negedge I2C_SCLK_in) begin
    if (RESET_in)
      I2C_SDA_TS_out <= 1;
    else begin
      if (i2c_start)
        I2C_SDA_TS_out <= 1;
      else if (i2c_lsb_bit) //acknowledge the end of a 1 byte transfer from master
        I2C_SDA_TS_out <= ! (((i2c_state==ST_I2C_GET_ADDR) && i2c_addr_match) || 
                             ((i2c_state==ST_I2C_GET_CMD ) && !(i2c_rd_cmd && i2c_byte_counter=='d3))  //send NACK at the last byte of command, only if read command
                            );
      else if ((i2c_ack_bit && //first bit of next slave to master transfer
               ((i2c_state==ST_I2C_GET_ADDR) && (i2c_drp_cmd==I2C_DRP_RD) )) || 
               (i2c_state==ST_I2C_READ && !i2c_rd_end)) //or read continued
        I2C_SDA_TS_out <= i2c_data_out[7];
      else
        I2C_SDA_TS_out <= 1;
    end
  end

  // clock stretching      
  assign I2C_SCLK_TS_out = 1'b1;
   
  //---- End of I2C logic ------------------------------------------------
  // Clock divider, generate  and adcclk

  always @(posedge DCLK_in)
    sysclk <= ~sysclk;

  always @(posedge DCLK_in ) begin
    if (curr_clkdiv_sel > 'd2 || clk_count_rst) begin
      if ((clk_count >= curr_clkdiv_sel-1) || clk_count_rst) 
        clk_count <= 0;
      else 
        clk_count <= clk_count + 1;

      if(clk_count_rst)
        adcclk_tmp <= 1;
      //else if(clk_count <= curr_clkdiv_sel/2 -2)
      else if(clk_count <= curr_clkdiv_sel/2 -1) //CR-1003761
        adcclk_tmp <= 1;
      else
        adcclk_tmp <= 0;
    end 
    else 
      adcclk_tmp <= ~adcclk_tmp;
  end

   wire adcclk_r;

  assign curr_clkdiv_sel = cfg_reg2[15:8];
       assign sysmone1_en = (cfg_reg2[5]===1 && cfg_reg2[4]===1) ? 0 : 1;
       assign sysmone12_en = (cfg_reg2[5]===1 ) ? 0 : 1;
  assign adcclk_div1 = (curr_clkdiv_sel > 'd2) ? 0 : 1;
       assign adcclk_r = (adcclk_div1) ? ~sysclk : adcclk_tmp;
       assign adcclk = (sysmone1_en) ? adcclk_r : 0;

  // end clock divider    
      
  // latch configuration registers
  wire [15:0] cfg_reg0_seq, cfg_reg0_adc;
  reg  [15:0] cfg_reg0_seq_tmp5, cfg_reg0_adc_tmp5;
  reg  [15:0] cfg_reg0_seq_tmp6, cfg_reg0_adc_tmp6;
  reg  [1:0]  acq_avg;

   

  //always @( seq1_0 or single_pass_finished or curr_seq_m  or cfg_reg0_adc or rst_in) begin
  always @(*) begin
    if (rst_in == 0) begin
      if ( default_mode) //default mode
        acq_chan_m = curr_seq_m[4:0];
      else if (cont_seq_mode || (single_pass_mode && !single_pass_finished))  //continuous mode or single pass active state
        acq_chan_m = curr_seq_m[4:0];
      else //single pass mode deactive state or single channel mode 
        acq_chan_m = cfg_reg0_adc[4:0];
    end
  end

  //CR 675227  always @( seq1_0 or single_pass_finished or curr_seq or cfg_reg0_adc or rst_in) begin
    always @(*) begin      
    if ((single_pass_mode  && !single_pass_finished) || 
         cont_seq_mode) //|| default_mode ) CR 927318: default mode doesn't support acq adjustability 
      acq_acqsel = curr_seq[8];
    else if (single_chan_mode) 
      acq_acqsel = cfg_reg0_adc[8];
    else 
      acq_acqsel = 0;
  end
      
  always @(single_pass_finished or curr_seq or cfg_reg0_adc or rst_in) begin      
    if (rst_in == 0) begin
      if (default_mode) begin  // default mode
        acq_avg  = 2'b01;
        acq_chan = curr_seq[5:0];
        acq_b_u  = 0;
      end
      //else if (!single_chan_mode && single_pass_finished == 0) begin // either continuous or single pass mode 
      else if (cont_seq_mode || (single_pass_mode && !single_pass_finished)) begin // either continuous or active single pass mode 
        acq_avg  = curr_seq[13:12];
        acq_chan = curr_seq[5:0];
        acq_b_u  = curr_seq[10];
      end
      else begin
        acq_avg  = cfg_reg0_adc[13:12];
        acq_chan = cfg_reg0_adc[5:0];
        acq_b_u  = cfg_reg0_adc[10];
       
        //CR 675227   
        // CR 764936        if (seq1_0 == 4'b0001) begin
        //when doing one pass when a CONVST BUSY should assert and then an EOC be seen, 
        //the user can assert a CONVST again without having to write to the sequence register to start the sequence again.
        if (single_pass_mode && !acq_e_c) begin // if single pass and not event driven
          halt_adc = halt_adc + 1;
          if (halt_adc == 2) //need to wait for EOS.
            dr_sram[8'h41][15:12] = SEQ_SINGLE_CHAN ;//4'b0011; //from single pass, go to single channel 
        end
      end
    end
  end

  reg single_chan_conv_end;
  reg [3:0] conv_end_reg_read;
  reg busy_reg_read;
  reg first_after_reset_tmp5;
  reg first_after_reset_tmp6;

  always@(posedge adcclk or posedge rst_in) begin
    if(rst_in) 
      conv_end_reg_read <= 4'b0;
    else       
      conv_end_reg_read <= {conv_end_reg_read[2:0], (single_chan_conv_end | conv_end)};
  end
        
  always@(posedge DCLK_in or posedge rst_in)   begin
    if(rst_in) 
      busy_reg_read <= 1;
    else       
      busy_reg_read <= ~conv_end_reg_read[2];
  end

// i2c write   
    assign cfg_reg0_adc =  (i2c_stop) ? cfg_reg0 : cfg_reg0_adc_tmp6;   
//    assign cfg_reg0_adc =  cfg_reg0_adc_tmp6; 
    assign cfg_reg0_seq =  cfg_reg0_seq_tmp6;
    assign acq_e_c =  acq_e_c_tmp6;

  always @(negedge BUSY_out or rst_in)
    if(rst_in) begin
      cfg_reg0_seq_tmp6 <= 16'b0;
      cfg_reg0_adc_tmp6 <= 16'b0;
      acq_e_c_tmp6 <= 0;
      first_after_reset_tmp6 <= 1;
    end
    else begin
      repeat(3) @(posedge DCLK);
      if(first_after_reset_tmp6) begin
        first_after_reset_tmp6<=0;
        cfg_reg0_adc_tmp6 <= cfg_reg0;
        cfg_reg0_seq_tmp6 <= cfg_reg0;
      end
      else begin
        cfg_reg0_adc_tmp6 <= cfg_reg0_seq;
        cfg_reg0_seq_tmp6 <= cfg_reg0;
      end
      acq_e_c_tmp6      <= cfg_reg0[9];
    end

  always @(posedge conv_start or  posedge busy_r_rst or posedge rst_in) 
    if (rst_in ==1)
      busy_r <= 0;
    else if (conv_start && rst_lock == 0)
      busy_r <= 1;
    else if (busy_r_rst)
      busy_r <= 0;
  
  always @(negedge BUSY_out )
    if (single_pass_finished == 1) //from single pass, go to single channel
      if (curr_seq1_0 == SEQ_SINGLE_PASS || curr_seq1_0 == SEQ_SINGLE_CHAN)  // CR 764936
        //when doing one pass when a CONVST BUSY should assert and then an EOC be seen, 
        //the user can assert a CONVST again without having to write to the sequence register to start the sequence again.
        curr_seq1_0 <= SEQ_SINGLE_CHAN; //4'b0011;
      else
        curr_seq1_0 <= SEQ_DEFAULT_MODE; //4'b0000; 
    else
      curr_seq1_0 <= seq1_0;

  always @(posedge conv_start or  rst_in ) 
    if (rst_in == 1) begin
      mn_mux_in <= 0.0;
        curr_chan <= 6'b0;
    end
    else  begin
      curr_chan         <= acq_chan;
      curr_seq1_0_lat   <= curr_seq1_0;

      if ((acq_chan == 3) || (acq_chan >= 16 && acq_chan <= 31)) begin
        if (ext_mux_en) begin
          tmp_v = $bitstoreal(mn_in_diff[ext_mux_chan]);
          mn_mux_in <= tmp_v; 
        end
        else begin
          tmp_v = $bitstoreal(mn_in_diff[acq_chan]);
          mn_mux_in <= tmp_v; 
        end
      end
      else
        mn_mux_in <= $bitstoreal(mn_in_uni[acq_chan]);
        
      if ( acq_chan == 7  || (acq_chan >= 9 && acq_chan <= 12) || acq_chan >= 36)
        $display("Warning: [Unisim %s-14] The analog channel %x at time %.3f ns is invalid. Check register 40h[5:0]. Instance: %m", MODULE_NAME, acq_chan, $time/1000.0);

        if ((single_pass_mode && !single_pass_finished) || cont_seq_mode || default_mode ) begin
          averaging   <= curr_seq[13:12];
          curr_b_u      <= curr_seq[10];
          curr_e_c      <= curr_seq[9];
          curr_acq      <= curr_seq[8];
        end
        else  begin
          averaging   <= acq_avg;
          curr_b_u      <= acq_b_u;
          curr_e_c      <= cfg_reg0[9];
          curr_acq      <= cfg_reg0[8];
        end
    end // if (rst_in == 0) 
    
  // end of latch configuration registers
    
  //----------------------------------------------------------------- 
  
  // sequence control


  always @(seq_en)
    seq_en_dly <= #1 seq_en;

  always @(posedge  seq_en_dly) begin
    if (single_pass_mode || cont_seq_mode) begin   //single pass or continuous sequence mode
      // high rate sequence
      hr_tot_chan = 0;
      for (si=0; si<= 15; si=si+1) begin
        if (seq_chan_reg1[si] ==1)  begin
          hr_tot_chan = hr_tot_chan + 1;
          seq_mem[hr_tot_chan] = si;   //seq_mem possible max is 33 - 1 = 32 max channels. Max allowed channels are 31.
        end
      end
      for (si=16; si<= 31; si=si+1) begin
        if (seq_chan_reg2[si-16] ==1) begin
          hr_tot_chan = hr_tot_chan + 1;
          seq_mem[hr_tot_chan] = si;
        end
      end
      for (si=32; si<= 35; si=si+1) begin
        if (seq_chan_reg3[si-32] ==1) begin
          hr_tot_chan = hr_tot_chan + 1;
          seq_mem[hr_tot_chan] = si;
        end
      end
    end
    else if (default_mode ) begin //default mode
      if(cfg_reg0[11]) 
        $display("Error: [Unisim %s-50] External mux selection will be disregarded as SYSMON is in default mode. Instance: %m", MODULE_NAME);

        hr_tot_chan = 5;
        seq_mem[1] = 0;
        seq_mem[2] = 8;
        seq_mem[3] = 9;
        seq_mem[4] = 10;
        seq_mem[5] = 14;
      end
  end //always


    always @( seq_count  or negedge seq_en_dly) begin
            seq_curr_i = seq_mem[seq_count];
         curr_seq = 16'b0;
      if (seq_curr_i >= 0 && seq_curr_i <= 15) begin
         curr_seq [2:0] =  seq_curr_i[2:0];
         curr_seq [4:3] = 2'b01;
         curr_seq [8]  = seq_acq_reg1[seq_curr_i];
         curr_seq [10] = seq_bu_reg1[seq_curr_i];
      
         if (default_mode)
           curr_seq [13:12] = 2'b01;
         else if (seq_avg_reg1[seq_curr_i])
           curr_seq [13:12] = cfg_reg0[13:12];
         else
           curr_seq [13:12] = 2'b00;
      
         if (seq_curr_i >= 0 && seq_curr_i <=7) 
           curr_seq [4:3] = 2'b01;
         else
           curr_seq [4:3] = 2'b00;
      end
      else if (seq_curr_i >= 16 && seq_curr_i <= 31) begin
         curr_seq [4:0] = seq_curr_i;
         curr_seq [8] = seq_acq_reg2[seq_curr_i - 16];
         curr_seq [10] = seq_bu_reg2[seq_curr_i - 16];
         if (seq_avg_reg2[seq_curr_i - 16] == 1)
           curr_seq [13:12] = cfg_reg0[13:12];
         else
           curr_seq [13:12] = 2'b00;
        end // if (seq_curr_i >= 16 && seq_curr_i <= 31)
      else if (seq_curr_i > 31 && seq_curr_i <= 35) begin
         curr_seq [5:0] = seq_curr_i;
         curr_seq [8] = seq_acq_reg3[seq_curr_i - 32];
         curr_seq [10] = seq_bu_reg3[seq_curr_i - 32];
         if (seq_avg_reg3[seq_curr_i - 32] == 1)
           curr_seq [13:12] = cfg_reg0[13:12];
         else
           curr_seq [13:12] = 2'b00;
      end
    end
   

    always @( seq_count_a  or negedge seq_en_dly) begin
        seq_curr_ia = seq_mem[seq_count_a];
    curr_seq_m = 16'b0;
    if (seq_curr_ia >= 0 && seq_curr_ia <= 15) begin
       curr_seq_m [2:0] =  seq_curr_ia[2:0];
       curr_seq_m [4:3] = 2'b01;
           curr_seq_m [8] = seq_acq_reg1[seq_curr_ia];
           curr_seq_m [10] = seq_bu_reg1[seq_curr_ia];

           if (seq1_0 == 4'b0000 ||  seq1_0[3:2] == 2'b11)
              curr_seq_m [13:12] = 2'b01;
           else if (seq_avg_reg1[seq_curr_ia] == 1)
              curr_seq_m [13:12] = cfg_reg0[13:12];
           else
              curr_seq_m [13:12] = 2'b00;

       if (seq_curr_ia >= 0 && seq_curr_ia <=7) 
         curr_seq_m [4:3] = 2'b01;
       else
         curr_seq_m [4:3] = 2'b00;
    end
    else if (seq_curr_ia >= 16 && seq_curr_ia <= 31) begin
           curr_seq_m [4:0] = seq_curr_ia;
           curr_seq_m [8] = seq_acq_reg2[seq_curr_ia - 16];
           curr_seq_m [10] = seq_bu_reg2[seq_curr_ia - 16];
           if (seq_avg_reg2[seq_curr_ia - 16] == 1)
              curr_seq_m [13:12] = cfg_reg0[13:12];
           else
              curr_seq_m [13:12] = 2'b00;
        end
    else if (seq_curr_ia > 31 && seq_curr_ia <= 35) begin
      curr_seq_m [5:0] = seq_curr_ia;
           curr_seq_m [8] = seq_acq_reg3[seq_curr_ia - 32];
           curr_seq_m [10] = seq_bu_reg3[seq_curr_ia - 32];
           if (seq_avg_reg3[seq_curr_ia - 32] == 1)
              curr_seq_m [13:12] = cfg_reg0[13:12];
           else
              curr_seq_m [13:12] = 2'b00;
    end
    end // always @ ( seq_count_a  or negedge seq_en_dly)
   

  always @(posedge BUSY_out or posedge rst_in ) begin
      if (rst_in == 1 || rst_lock == 1 )
        seq_count_a <= 1;
      else  begin
        if ( curr_seq1_0_lat == SEQ_SINGLE_CHAN )
          seq_count_a <= 1;
        else  begin
          if (seq_count_a >= 37 || seq_count_a >= hr_tot_chan) 
            seq_count_a <= 1;
          else
            seq_count_a <= seq_count_a +1;
        end
      end
  end //always
   


  always @(posedge adcclk or posedge rst_in)
      if (rst_in == 1 ) begin
        seq_count <= 1;
        eos_en <= 0;
      end
      else  begin

       if ((seq_count == hr_tot_chan) &&
          (adc_state == S3_ST && adc_next_state == S5_ST) &&
          (curr_seq1_0_lat != SEQ_SINGLE_CHAN) && rst_lock == 0)
          eos_tmp_en <= 1;
        else
          eos_tmp_en <= 0;
       
     if (eos_tmp_en == 1 && seq_status_avg == 0 ) // delay by 1 adcclk
          eos_en <= 1;
        else
          eos_en <= 0;

        if (eos_tmp_en == 1 || (curr_seq1_0_lat == SEQ_SINGLE_CHAN)) begin
          seq_count <= 1;
        end
        else if (seq_count_en == 1) begin
          if (seq_count >= 37) 
                seq_count <= 1;
          else
            seq_count <= seq_count +1;
        end
      end // else: !if(rst_in == 1 )
    
// end sequence control
    
  // Acquisition
  reg first_acq;
  reg shorten_acq;
  wire BUSY_out_dly;

  assign #10 BUSY_out_dly = BUSY_out;

  always @(adc_state or posedge rst_in or first_acq)  begin
    if(rst_in) 
      shorten_acq = 0;
    else if(BUSY_out_dly==0 && adc_state==S2_ST && first_acq==1)
      shorten_acq = 1;
    else
      shorten_acq = 0;
  end

  always @(posedge adcclk or posedge rst_in)
    if (rst_in == 1 || rst_lock == 1) begin
      acq_count <= 1;
      first_acq <= 1;
    end
    else  begin 
      if (adc_state == S2_ST && rst_lock == 0 && (acq_e_c==0)) begin
        first_acq <= 0;
        if (acq_acqsel == 1) begin
          if (acq_count <= 11)
            acq_count <= acq_count + 1 + shorten_acq;
        end
        else begin
          if (acq_count <= 4)
            acq_count <= acq_count + 1 + shorten_acq;
        end // else: !if(acq_acqsel == 1)
             
        if (adc_next_state == S3_ST)
          if ((acq_acqsel == 1 && acq_count < 10) || (acq_acqsel == 0 && acq_count < 4))
            $display ("Warning: [Unisim %s-21] Acquisition time is not long enough at time %t. Instance: %m", MODULE_NAME, $time);
      end // if (adc_state == S2_ST)
      else
        acq_count <=  (first_acq) ? 1 : 0;
    end // if (rst_in == 0)

  // continuous mode
  reg  conv_start_cont;
  wire reset_conv_start;
  wire conv_start_sel;

  always @(adc_state or acq_acqsel or acq_count)
     if (adc_state == S2_ST) begin
       if (rst_lock == 0) begin
         // CR 800173  
         // if ( ((seq_reset_flag == 0 || (seq_reset_flag == 1 && curr_clkdiv_sel > 8'h03)) &&
         //      ( (acq_acqsel == 1 && acq_count > 10) || (acq_acqsel == 0 && acq_count > 4)) ) )
         if ((acq_acqsel == 1 && acq_count > 10) || (acq_acqsel == 0 && acq_count > 4))  // acq time, adcclk cycles 4 or 10
           conv_start_cont = 1;
         else
           conv_start_cont = 0;
        end
     end // if (adc_state == S2_ST)
     else
       conv_start_cont = 0;
   
  
  assign conv_start_sel = (acq_e_c) ? CONVST_reg : conv_start_cont;
  assign reset_conv_start = rst_in | (conv_count==CONV_CAL_PER_0);
   
  always@(posedge conv_start_sel or posedge reset_conv_start)   begin
    if(reset_conv_start) 
      conv_start <= 0;
    else                 
      conv_start <= 1;
  end


// end acquisition    
    
// Conversion
  always @(adc_state or adc_next_state or curr_chan  or mn_mux_in or curr_b_u) begin
    if ((adc_state == S3_ST && adc_next_state == S5_ST) ||  adc_state == S5_ST) begin
        if (curr_chan == 0) begin    // temperature conversion
           adc_temp_result = (mn_mux_in + 273.6777) * 0.0019945*65536.0; //CR 861679

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
      else if (curr_chan == 1 || curr_chan == 2 || curr_chan ==6 ||
               curr_chan == 13 || curr_chan == 14 || curr_chan ==  15 || 
               (curr_chan >= 32 && curr_chan <= 35)) begin     // internal power conversion
        adc_intpwr_result = mn_mux_in * 65536.0 / 3.0;
        if (adc_intpwr_result >= 65535.0)
          conv_result_int = 65535;
        else if (adc_intpwr_result < 0.0)
          conv_result_int = 0;
        else begin
          conv_result_int = $rtoi(adc_intpwr_result);
          if (adc_intpwr_result - conv_result_int > 0.9999)
            conv_result_int = conv_result_int + 1;
        end
      end
      else if (curr_chan == 3 || (curr_chan >=16 && curr_chan <= 31)) begin
        adc_ext_result =  (mn_mux_in) * 65536.0;
        if (curr_b_u == 1) begin
          if (adc_ext_result > 32767.0)
            conv_result_int = 32767;
          else if (adc_ext_result < -32768.0)
            conv_result_int = -32768;
          else begin
            conv_result_int = $rtoi(adc_ext_result);
            if (adc_ext_result - conv_result_int > 0.9999)
               conv_result_int = conv_result_int + 1;
          end
        end
      else begin
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
    else begin
      conv_result_int = 0;
    end
  end 

  conv_result = conv_result_int;
    
  end // always @ ( adc_state or curr_chan or mn_mux_in, curr_b_u)

    
  reg busy_r_rst_done;
    
  always @(posedge adcclk or  posedge rst_in) begin
    if (rst_in == 1) begin
      busy_r_rst <= 0;        
      busy_r_rst_done <= 0;
      conv_count <= CONV_CAL_PER_RST;
      conv_end <= 0;
    end
    else begin
      if(adc_state == S2_ST)      begin
        busy_r_rst_done <= 1;
        busy_r_rst      <= (!busy_r_rst_done) ? 1 : 0;
        if (conv_start == 1) begin
          conv_count <= 0;
          conv_end   <= 0;
        end
      end
      else if (adc_state == S3_ST ) begin
        busy_r_rst_done <= 0;
        conv_count = conv_count + 1;
        if ((curr_chan!=5'b01000 ) && (conv_count==CONV_NOTCAL_PER_1 ) ||
            (curr_chan==5'b01000 ) && (conv_count==CONV_CAL_PER_2 ) && (first_cal_chan) ||
            (curr_chan==5'b01000 ) && (conv_count==CONV_CAL_PER_3 ) && (!first_cal_chan))
          conv_end <= 1;
        else
          conv_end <= 0;
      end
      else begin //all other adc_state's except for S2_ST and S3_ST
        conv_end   <= 0;
        conv_count <= 0;
      end
    end
  end//always

  always @(posedge adcclk or  posedge rst_in) begin
    if (rst_in == 1)
      conv_result_reg <= 0;
    else begin
      if (adc_state == S5_ST) 
       conv_result_reg <= conv_result;
    end
  end

  always @(posedge adcclk or  posedge rst_in) begin
    if (rst_in == 1)
      single_chan_conv_end <= 0;
    else begin
      // jmcgrath - to model the behaviour correctly when a cal chanel is being converted
      // an signal to signify the conversion has ended must be produced - this is for single channel mode
      single_chan_conv_end <= 0;
      if( (conv_count ==CONV_NOTCAL_PER_1) || (conv_count == CONV_CAL_PER_4)) 
          single_chan_conv_end <= 1;
    end
  end

  assign avg_amount = averaging==2'b00 ? 0   :
                      averaging==2'b01 ? 15  :
                      averaging==2'b10 ? 63  :
                                         255 ; //2'b11
              
  always @(posedge adcclk or  posedge rst_in) begin
    if (rst_in == 1) begin
      seq_status_avg <= 0;
      for (i = 0; i <=35; i = i +1) begin
        conv_avg_count[i] <= 0;     // array of integer
      end
    end
    else begin
      if (adc_state == S3_ST && adc_next_state == S5_ST && rst_lock == 0) begin
        if(averaging==2'b00) begin
          eoc_en <= 1;
          conv_avg_count[curr_chan] <= 0;
        end
        else begin //averaging is on
          if (conv_avg_count[curr_chan] == avg_amount) begin
            eoc_en <= 1;
            conv_avg_count[curr_chan] <= 0;
              seq_status_avg <= seq_status_avg - 1;
          end
          else begin
            eoc_en <= 0;
            if (conv_avg_count[curr_chan] == 0) begin
                seq_status_avg <= seq_status_avg + 1;
            end
            conv_avg_count[curr_chan] <= conv_avg_count[curr_chan] + 1;
          end
        end // averaging>0
      end // if (adc_state == S3_ST && adc_next_state == S5_ST)
      else  begin
        eoc_en <= 0;
      end
    end // else
  end //always
  // end conversion

    
  // average
   always @(adc_state or conv_acc[curr_chan]) 
    if (adc_state == S5_ST ) 
        // no signed or unsigned differences for bit vector conv_acc_vec
        conv_acc_vec = conv_acc[curr_chan];
    else
        conv_acc_vec = 24'd0;


    always @(posedge adcclk or posedge rst_in) 
      if (rst_in == 1) begin
     for (j = 0; j <= 63; j = j + 1) begin
        conv_acc[j] <= 0;
     end
     conv_acc_result <= 16'd0;
      end
      else  begin
     if (adc_state == S3_ST && adc_next_state == S5_ST) begin
        if (averaging != 2'b00 && rst_lock != 1)
          conv_acc[curr_chan] <= conv_acc[curr_chan] + conv_result_int;
        else
          conv_acc[curr_chan] <= 0;
     end // if (adc_state == S3_ST && adc_next_state == S5_ST)
     else if (eoc_en == 1) begin
        case (averaging)
              2'b00 : conv_acc_result <= 16'd0;
              2'b01 : conv_acc_result <= conv_acc_vec[19:4];
              2'b10 : conv_acc_result <= conv_acc_vec[21:6];
              2'b11 : conv_acc_result <= conv_acc_vec[23:8];
        endcase 
        conv_acc[curr_chan] <= 0;
     end 
      end // if (rst_in == 0)
   
  // end average    
        
  // single sequence
  always @(posedge adcclk or posedge rst_in) begin 
    if (rst_in == 1)
      single_pass_finished <= 0;
    else  
      if (adc_state == S1_ST)
        single_pass_finished <= 1; //single pass sequence selected and sequence has ended.
  end
  //  end state    

  always @(posedge adcclk or posedge rst_in)
  if (rst_in) begin
    seq_count_en <= 0;
    EOS_out_tmp <= 0;
    EOC_out_tmp <= 0;
  end 
  else  begin
    if ((adc_state == S3_ST && adc_next_state == S5_ST) && (curr_seq1_0_lat != SEQ_SINGLE_CHAN ) && !rst_lock )
      seq_count_en <= 1;
    else
      seq_count_en <= 0;
    
    if (!rst_lock) begin
      EOS_out_tmp <= eos_en;
      eoc_en_delay <= eoc_en;
      EOC_out_tmp <= eoc_en_delay;
    end 
    else begin
      EOS_out_tmp <= 0;
      eoc_en_delay <= 0;
      EOC_out_tmp <= 0;
    end
  end



  always @(posedge EOC_out_pre2 or posedge rst_in_not_seq) begin
    if (rst_in_not_seq == 1) begin
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
    end 
    else if ( rst_lock == 0) begin //also posedge EOC_out_pre2
      // current or averaged values' update to status registers
      if ((curr_chan_lat >= 0 && curr_chan_lat <= 3)  || (curr_chan_lat == 6) ||
          (curr_chan_lat >= 13 && curr_chan_lat <= 31)) begin
        if (averaging_d == 2'b00)
          data_reg[curr_chan_lat] <= conv_result_reg;
        else
          data_reg[curr_chan_lat] <= conv_acc_result;
      end
      else if (curr_chan_lat >= 32 && curr_chan_lat <= 35) begin //VUser0-3
        if (averaging_d == 2'b00)
          dr_sram[curr_chan_lat + 96] <= conv_result_reg; //80h-83h
        else
          dr_sram[curr_chan_lat + 96] <= conv_acc_result;
      end
      else if (curr_chan_lat == 4) // VREFP
        data_reg[curr_chan_lat] <= 16'h0000; // CR-961722 Simulation always simulates the internal reference behavior. Hence VrefP=0V
      else if (curr_chan_lat == 5) // VREFN
        data_reg[curr_chan_lat] <= 16'h0000;

      //min and max values' update
      if (curr_chan_lat == 0 || curr_chan_lat == 1 || curr_chan_lat == 2) begin //TEMPERATURE, VCCINT and VCCAUX max and min
        if (averaging_d == 2'b00) begin
          if (conv_result_reg > data_reg[32 + curr_chan_lat])
            data_reg[32 + curr_chan_lat] <= conv_result_reg;
          if (conv_result_reg < data_reg[36 + curr_chan_lat])
            data_reg[36 + curr_chan_lat] <= conv_result_reg;
        end
        else begin
          if (conv_acc_result > data_reg[32 + curr_chan_lat])
            data_reg[32 + curr_chan_lat] <= conv_acc_result;
          if (conv_acc_result < data_reg[36 + curr_chan_lat])
            data_reg[36 + curr_chan_lat] <= conv_acc_result;
        end  
      end

      else if (curr_chan_lat == 6) begin //VCCBRAM max and min
        if (averaging_d == 2'b00) begin
          if (conv_result_reg > data_reg[35])
            data_reg[35] <= conv_result_reg;
          if (conv_result_reg < data_reg[39])
            data_reg[39] <= conv_result_reg;
        end
        else begin
          if (conv_acc_result > data_reg[35])
            data_reg[35] <= conv_acc_result;
          if (conv_acc_result < data_reg[39])
            data_reg[39] <= conv_acc_result;
        end
      end
      else if (curr_chan_lat >= 13 && curr_chan_lat <= 15) begin  // VPSINTLP, VPSINTFP , VPSAUX
        if (averaging_d == 2'b00) begin
          if (conv_result_reg > data_reg[27+curr_chan_lat])
            data_reg[27+curr_chan_lat] <= conv_result_reg;
          if (conv_result_reg < data_reg[31+curr_chan_lat])
            data_reg[31+curr_chan_lat] <= conv_result_reg;
        end
        else begin
          if (conv_acc_result > data_reg[27+curr_chan_lat])
            data_reg[27+curr_chan_lat] <= conv_acc_result;
          if (conv_acc_result < data_reg[31+curr_chan_lat])
            data_reg[31+curr_chan_lat] <= conv_acc_result;
        end
      end
      else if (curr_chan_lat >= 32 && curr_chan_lat <=35) begin   //Vuser0-3
        if (averaging_d == 2'b00) begin
          if (conv_result_reg < dr_sram[curr_chan_lat+136])
            dr_sram[curr_chan_lat+136] <= conv_result_reg;
          if (conv_result_reg > dr_sram[curr_chan_lat+128])
            dr_sram[curr_chan_lat+128] <= conv_result_reg;
        end
        else begin
          if (conv_acc_result < dr_sram[curr_chan_lat+136])
            dr_sram[curr_chan_lat+136] <= conv_acc_result;
          if (conv_acc_result > dr_sram[curr_chan_lat+128])
            dr_sram[curr_chan_lat+128] <= conv_acc_result;
        end
      end

    end //  ( rst_lock == 0)
  end//always


  // current measurement data
  always @(negedge busy_r or posedge rst_in_not_seq )
    if (rst_in_not_seq)
      data_written <= 16'd0;
    else begin
      if (averaging == 2'b00) 
        data_written <= conv_result_reg;
      else
        data_written <= conv_acc_result;
    end


    reg [4:0] op_count=15;
    reg       BUSY_out_sync;
    wire      BUSY_out_low_edge;
    
// eos and eoc

  always @( posedge EOC_out_tmp or posedge EOC_out or posedge rst_in)
    if (rst_in ==1)
      EOC_out_tmp1 <= 0;
    else if ( EOC_out ==1)
      EOC_out_tmp1 <= 0;
    else if (EOC_out_tmp == 1) begin
      if (curr_chan != 5'b01000 && ( sysmone12_en == 1 || (curr_seq1_0[3:2] != 2'b10 && sysmone12_en == 0))) //not calibration and check power   
        EOC_out_tmp1 <= 1; 
      else
        EOC_out_tmp1 <= 0;
    end

    always @( posedge EOS_out_tmp or posedge EOS_out or posedge rst_in)
           if (rst_in ==1)
              EOS_out_tmp1 <= 0;
           else if (EOS_out ==1)
               EOS_out_tmp1 <= 0;
           else if (EOS_out_tmp == 1 &&  ( sysmone12_en == 1 || (curr_seq1_0[3:2] != 2'b10 && sysmone12_en == 0)))    
               EOS_out_tmp1 <= 1; 

  assign BUSY_out_low_edge = (BUSY_out==0 && BUSY_out_sync==1) ? 1 : 0;

  always @( posedge DCLK_in or posedge rst_in) begin
    if (rst_in) 
      op_count <= 15;
    else begin
      if (BUSY_out_low_edge==1 )
        op_count <= 0;
      else if(op_count < 22)
        op_count <= op_count +1;
    end
  end

  always @(posedge DCLK_in or posedge rst_in) begin
    if (rst_in) begin
      EOC_out  <= 0;
      EOS_out  <= 0;
      EOC_out_pre  <= 0;
      EOC_out_pre2 <= 0;
    end
    else begin
      if(op_count== 16) begin
        EOC_out  <= EOC_out_tmp1;
        EOS_out  <= EOS_out_tmp1;
        EOC_out_pre  <=0;
        EOC_out_pre2 <=0;
      end
      else if (op_count==15) begin
        EOC_out  <= 0;
        EOS_out  <= 0;
        EOC_out_pre  <= EOC_out_tmp1;
        EOC_out_pre2 <=0;
      end
      else if (op_count==14) begin
        EOC_out  <= 0;
        EOS_out  <= 0;
        EOC_out_pre  <=0;
        EOC_out_pre2 <= EOC_out_tmp1;
      end
      else begin
        EOC_out  <= 0;
        EOS_out  <= 0;
        EOC_out_pre  <= 0;
        EOC_out_pre2 <= 0;
      end
    end
  end

  always @( posedge DCLK_in or posedge rst_in) begin
    if (rst_in) begin
      BUSY_out_sync <= 0;
      drp_update    <= 0;
      alm_update  <= 0;
    end
    else begin // if(rst_in==0)  begin
      BUSY_out_sync <= BUSY_out;
      drp_update    <= (op_count==3)? 1 : 0;
      alm_update  <= (op_count==5 && EOC_out_tmp1==1) ? 1 : 0;
    end
  end

// end eos and eoc

// alarm

  always @( posedge alm_update or posedge rst_in_not_seq ) begin
    if (rst_in_not_seq == 1) begin
      ot_out_reg <= 0;
      alm_out_reg <= 8'b0;
    end
    else if (rst_lock == 0) begin
      if (curr_chan_lat == 0) begin // temperature 
        if (data_written >= ot_limit_reg)
          ot_out_reg <= 1;
        else if (data_written < dr_sram[8'h57]) 
          ot_out_reg <= 0;

        if (data_written > dr_sram[8'h50])  
          alm_out_reg[0] <= 1;
        else if (data_written < dr_sram[8'h54])
          alm_out_reg[0] <= 0;
      end
   
      if (curr_chan_lat == 1) begin // VCC INT
        if (data_written > dr_sram[8'h51] || data_written < dr_sram[8'h55])
          alm_out_reg[1] <= 1;
        else
          alm_out_reg[1] <= 0;
      end

      if (curr_chan_lat == 2) begin //VCCAUX
        if (data_written > dr_sram[8'h52] || data_written < dr_sram[8'h56])
          alm_out_reg[2] <= 1;
        else
          alm_out_reg[2] <= 0;
      end

      if (curr_chan_lat == 6) begin // VCC BRAM
        if (data_written > dr_sram[8'h58] || data_written < dr_sram[8'h5C])
          alm_out_reg[3] <= 1;
        else
          alm_out_reg[3] <= 0;
      end
      if (curr_chan_lat == 13) begin //VCC PSINTLP
        if (data_written > dr_sram[8'h59] || data_written < dr_sram[8'h5D])
          alm_out_reg[4] <= 1;
        else
          alm_out_reg[4] <= 0;
        end
        if (curr_chan_lat == 14) begin // VCC PSINTFP
          if (data_written > dr_sram[8'h5A] || data_written < dr_sram[8'h5E])
            alm_out_reg[5] <= 1;
          else
            alm_out_reg[5] <= 0;
         end
         if (curr_chan_lat == 15) begin // VCC PSAUX
           if (data_written > dr_sram[8'h5B] || data_written < dr_sram[8'h5F])
             alm_out_reg[6] <= 1;
           else
             alm_out_reg[6] <= 0;
         end
         if (curr_chan_lat == 32) begin // VUSER 0
           if (data_written > dr_sram[8'h60] || data_written < dr_sram[8'h68])
             alm_out_reg[8] <= 1;
           else
             alm_out_reg[8] <= 0;
         end
      if (curr_chan_lat == 33) begin // VUSER 1
        if (data_written > dr_sram[8'h61] || data_written < dr_sram[8'h69])
          alm_out_reg[9] <= 1;
        else
          alm_out_reg[9] <= 0;
        end
      if (curr_chan_lat == 34) begin // VUSER 2
        if (data_written > dr_sram[8'h62] || data_written < dr_sram[8'h6A])
          alm_out_reg[10] <= 1;
        else
          alm_out_reg[10] <= 0;
        end
      if (curr_chan_lat == 35) begin // VUSER 3
        if (data_written > dr_sram[8'h63] || data_written < dr_sram[8'h6B])
          alm_out_reg[11] <= 1;
        else
          alm_out_reg[11] <= 0;
      end
    end//rst_lock
    end // always 

  //always @(ot_out_reg or ot_en or alm_out_reg or alm_en) begin
  always @(*) begin
    OT_out = ot_out_reg & ot_en;

    ALM_out[6:0]   = alm_out_reg[6:0] & alm_en[6:0];
    ALM_out[7]     = |ALM_out[6:0];
    ALM_out[11:8]  = alm_out_reg[11:8] & alm_en[11:8];
    ALM_out[14:12] = 'd0; // Reserved
    ALM_out[15]    = (|ALM_out[11:8]) | (|ALM_out[6:0]);
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
      curr_chan = 5'bx;
      DRDY_out = 1'bx;
      DO_out = 16'bx;
   end 

   always @(notifier_do) begin
      DRDY_out = 1'bx;
      DO_out = 16'bx;
   end


`endif
   
  specify
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
    (DCLK => JTAGBUSY) = (100:100:100, 100:100:100);
    (DCLK => JTAGLOCKED) = (100:100:100, 100:100:100);
    (DCLK => JTAGMODIFIED) = (100:100:100, 100:100:100);
    (DCLK => MUXADDR[0]) = (100:100:100, 100:100:100);
    (DCLK => MUXADDR[1]) = (100:100:100, 100:100:100);
    (DCLK => MUXADDR[2]) = (100:100:100, 100:100:100);
    (DCLK => MUXADDR[3]) = (100:100:100, 100:100:100);
    (DCLK => MUXADDR[4]) = (100:100:100, 100:100:100);
    (DCLK => OT) = (100:100:100, 100:100:100);
  `ifdef XIL_TIMING
    $period (negedge CONVST, 0:0:0, notifier);
    $period (negedge CONVSTCLK, 0:0:0, notifier);
    $period (negedge DCLK, 0:0:0, notifier);
    $period (posedge CONVST, 0:0:0, notifier);
    $period (posedge CONVSTCLK, 0:0:0, notifier);
    $period (posedge DCLK, 0:0:0, notifier);
    $recrem (negedge RESET, negedge DCLK, 0:0:0, 0:0:0, notifier, dclk_en_n, dclk_en_n, RESET_delay, DCLK_delay);
    $recrem (negedge RESET, posedge DCLK, 0:0:0, 0:0:0, notifier, dclk_en_p, dclk_en_p, RESET_delay, DCLK_delay);
    $recrem (posedge RESET, negedge DCLK, 0:0:0, 0:0:0, notifier, dclk_en_n, dclk_en_n, RESET_delay, DCLK_delay);
    $recrem (posedge RESET, posedge DCLK, 0:0:0, 0:0:0, notifier, dclk_en_p, dclk_en_p, RESET_delay, DCLK_delay);
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

  //`undef    CALIBRATION_ALWAYS_FIRST   

endmodule 

`endcelldefine
