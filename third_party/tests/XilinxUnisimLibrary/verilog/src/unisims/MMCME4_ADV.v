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
//  /   /                        Advanced Mixed Mode Clock Manager (MMCM)
// /___/   /\      Filename    : MMCME4_ADV.v
// \   \  /  \
//  \___\/\___\
//
///////////////////////////////////////////////////////////////////////////////
//  Revision:
//  03/21/2013   - YML changes
//  03/22/2013   - 708090 - Change error to Warning
//  03/27/2013   - Update with writer notation
//  04/04/2013   - 709484 - Add PFD check
//  04/04/2013   - 709093 - Fix periods after DRP
//  04/12/2013   - invertible pin changes
//  04/22/2013   - 713991 - Fix cddcdone assertion
//  04/24/2013   - 709726 - fix vcoflag
//  05/07/2013   - 714319 - fix phase warning
//  10/22/2014 808642 - Added #1 to $finish
//  End Revision:
///////////////////////////////////////////////////////////////////////////////

`timescale 1 ps / 1 ps

`celldefine

module MMCME4_ADV #(
`ifdef XIL_TIMING
  parameter LOC = "UNPLACED",
  parameter real CLKIN_FREQ_MAX = 1066.000,
  parameter real CLKIN_FREQ_MIN = 10.000,
  parameter real CLKPFD_FREQ_MAX = 550.000,
  parameter real CLKPFD_FREQ_MIN = 10.000,
  parameter real VCOCLK_FREQ_MAX = 1600.000,
  parameter real VCOCLK_FREQ_MIN = 800.000,
`endif
  parameter BANDWIDTH = "OPTIMIZED",
  parameter real CLKFBOUT_MULT_F = 5.000,
  parameter real CLKFBOUT_PHASE = 0.000,
  parameter CLKFBOUT_USE_FINE_PS = "FALSE",
  parameter real CLKIN1_PERIOD = 0.000,
  parameter real CLKIN2_PERIOD = 0.000,
  parameter real CLKOUT0_DIVIDE_F = 1.000,
  parameter real CLKOUT0_DUTY_CYCLE = 0.500,
  parameter real CLKOUT0_PHASE = 0.000,
  parameter CLKOUT0_USE_FINE_PS = "FALSE",
  parameter integer CLKOUT1_DIVIDE = 1,
  parameter real CLKOUT1_DUTY_CYCLE = 0.500,
  parameter real CLKOUT1_PHASE = 0.000,
  parameter CLKOUT1_USE_FINE_PS = "FALSE",
  parameter integer CLKOUT2_DIVIDE = 1,
  parameter real CLKOUT2_DUTY_CYCLE = 0.500,
  parameter real CLKOUT2_PHASE = 0.000,
  parameter CLKOUT2_USE_FINE_PS = "FALSE",
  parameter integer CLKOUT3_DIVIDE = 1,
  parameter real CLKOUT3_DUTY_CYCLE = 0.500,
  parameter real CLKOUT3_PHASE = 0.000,
  parameter CLKOUT3_USE_FINE_PS = "FALSE",
  parameter CLKOUT4_CASCADE = "FALSE",
  parameter integer CLKOUT4_DIVIDE = 1,
  parameter real CLKOUT4_DUTY_CYCLE = 0.500,
  parameter real CLKOUT4_PHASE = 0.000,
  parameter CLKOUT4_USE_FINE_PS = "FALSE",
  parameter integer CLKOUT5_DIVIDE = 1,
  parameter real CLKOUT5_DUTY_CYCLE = 0.500,
  parameter real CLKOUT5_PHASE = 0.000,
  parameter CLKOUT5_USE_FINE_PS = "FALSE",
  parameter integer CLKOUT6_DIVIDE = 1,
  parameter real CLKOUT6_DUTY_CYCLE = 0.500,
  parameter real CLKOUT6_PHASE = 0.000,
  parameter CLKOUT6_USE_FINE_PS = "FALSE",
  parameter COMPENSATION = "AUTO",
  parameter integer DIVCLK_DIVIDE = 1,
  parameter [0:0] IS_CLKFBIN_INVERTED = 1'b0,
  parameter [0:0] IS_CLKIN1_INVERTED = 1'b0,
  parameter [0:0] IS_CLKIN2_INVERTED = 1'b0,
  parameter [0:0] IS_CLKINSEL_INVERTED = 1'b0,
  parameter [0:0] IS_PSEN_INVERTED = 1'b0,
  parameter [0:0] IS_PSINCDEC_INVERTED = 1'b0,
  parameter [0:0] IS_PWRDWN_INVERTED = 1'b0,
  parameter [0:0] IS_RST_INVERTED = 1'b0,
  parameter real REF_JITTER1 = 0.010,
  parameter real REF_JITTER2 = 0.010,
  parameter SS_EN = "FALSE",
  parameter SS_MODE = "CENTER_HIGH",
  parameter integer SS_MOD_PERIOD = 10000,
  parameter STARTUP_WAIT = "FALSE"
)(
  output CDDCDONE,
  output CLKFBOUT,
  output CLKFBOUTB,
  output CLKFBSTOPPED,
  output CLKINSTOPPED,
  output CLKOUT0,
  output CLKOUT0B,
  output CLKOUT1,
  output CLKOUT1B,
  output CLKOUT2,
  output CLKOUT2B,
  output CLKOUT3,
  output CLKOUT3B,
  output CLKOUT4,
  output CLKOUT5,
  output CLKOUT6,
  output [15:0] DO,
  output DRDY,
  output LOCKED,
  output PSDONE,

  input CDDCREQ,
  input CLKFBIN,
  input CLKIN1,
  input CLKIN2,
  input CLKINSEL,
  input [6:0] DADDR,
  input DCLK,
  input DEN,
  input [15:0] DI,
  input DWE,
  input PSCLK,
  input PSEN,
  input PSINCDEC,
  input PWRDWN,
  input RST
);

`ifndef XIL_TIMING
  localparam real CLKIN_FREQ_MAX = 1066.000;
  localparam real CLKIN_FREQ_MIN = 10.000;
  localparam real CLKPFD_FREQ_MAX = 550.000;
  localparam real CLKPFD_FREQ_MIN = 10.000;
  localparam real VCOCLK_FREQ_MAX = 1600.000;
  localparam real VCOCLK_FREQ_MIN = 800.000;
`endif

// define constants
  localparam MODULE_NAME = "MMCME4_ADV";

// Parameter encodings and registers
  localparam BANDWIDTH_HIGH = 1;
  localparam BANDWIDTH_LOW = 2;
  localparam BANDWIDTH_OPTIMIZED = 0;
  localparam CLKFBOUT_USE_FINE_PS_FALSE = 0;
  localparam CLKFBOUT_USE_FINE_PS_TRUE = 1;
  localparam CLKOUT0_USE_FINE_PS_FALSE = 0;
  localparam CLKOUT0_USE_FINE_PS_TRUE = 1;
  localparam CLKOUT1_USE_FINE_PS_FALSE = 0;
  localparam CLKOUT1_USE_FINE_PS_TRUE = 1;
  localparam CLKOUT2_USE_FINE_PS_FALSE = 0;
  localparam CLKOUT2_USE_FINE_PS_TRUE = 1;
  localparam CLKOUT3_USE_FINE_PS_FALSE = 0;
  localparam CLKOUT3_USE_FINE_PS_TRUE = 1;
  localparam CLKOUT4_CASCADE_FALSE = 0;
  localparam CLKOUT4_CASCADE_TRUE = 1;
  localparam CLKOUT4_USE_FINE_PS_FALSE = 0;
  localparam CLKOUT4_USE_FINE_PS_TRUE = 1;
  localparam CLKOUT5_USE_FINE_PS_FALSE = 0;
  localparam CLKOUT5_USE_FINE_PS_TRUE = 1;
  localparam CLKOUT6_USE_FINE_PS_FALSE = 0;
  localparam CLKOUT6_USE_FINE_PS_TRUE = 1;
  localparam COMPENSATION_AUTO = 0;
  localparam COMPENSATION_BUF_IN = 1;
  localparam COMPENSATION_EXTERNAL = 2;
  localparam COMPENSATION_INTERNAL = 3;
  localparam COMPENSATION_ZHOLD = 4;
  localparam SS_EN_FALSE = 0;
  localparam SS_EN_TRUE = 1;
  localparam SS_MODE_CENTER_HIGH = 0;
  localparam SS_MODE_CENTER_LOW = 1;
  localparam SS_MODE_DOWN_HIGH = 2;
  localparam SS_MODE_DOWN_LOW = 3;
  localparam STARTUP_WAIT_FALSE = 0;
  localparam STARTUP_WAIT_TRUE = 1;

  reg trig_attr;
// include dynamic registers - XILINX test only
`ifdef XIL_DR
  `include "MMCME4_ADV_dr.v"
`else
  localparam [72:1] BANDWIDTH_REG = BANDWIDTH;
  localparam real CLKFBOUT_MULT_F_REG = CLKFBOUT_MULT_F;
  localparam real CLKFBOUT_PHASE_REG = CLKFBOUT_PHASE;
  localparam [40:1] CLKFBOUT_USE_FINE_PS_REG = CLKFBOUT_USE_FINE_PS;
  localparam real CLKIN1_PERIOD_REG = CLKIN1_PERIOD;
  localparam real CLKIN2_PERIOD_REG = CLKIN2_PERIOD;
  localparam real CLKIN_FREQ_MAX_REG = CLKIN_FREQ_MAX;
  localparam real CLKIN_FREQ_MIN_REG = CLKIN_FREQ_MIN;
  localparam real CLKOUT0_DIVIDE_F_REG = CLKOUT0_DIVIDE_F;
  localparam real CLKOUT0_DUTY_CYCLE_REG = CLKOUT0_DUTY_CYCLE;
  localparam real CLKOUT0_PHASE_REG = CLKOUT0_PHASE;
  localparam [40:1] CLKOUT0_USE_FINE_PS_REG = CLKOUT0_USE_FINE_PS;
  localparam [31:0] CLKOUT1_DIVIDE_REG = CLKOUT1_DIVIDE;
  localparam real CLKOUT1_DUTY_CYCLE_REG = CLKOUT1_DUTY_CYCLE;
  localparam real CLKOUT1_PHASE_REG = CLKOUT1_PHASE;
  localparam [40:1] CLKOUT1_USE_FINE_PS_REG = CLKOUT1_USE_FINE_PS;
  localparam [31:0] CLKOUT2_DIVIDE_REG = CLKOUT2_DIVIDE;
  localparam real CLKOUT2_DUTY_CYCLE_REG = CLKOUT2_DUTY_CYCLE;
  localparam real CLKOUT2_PHASE_REG = CLKOUT2_PHASE;
  localparam [40:1] CLKOUT2_USE_FINE_PS_REG = CLKOUT2_USE_FINE_PS;
  localparam [31:0] CLKOUT3_DIVIDE_REG = CLKOUT3_DIVIDE;
  localparam real CLKOUT3_DUTY_CYCLE_REG = CLKOUT3_DUTY_CYCLE;
  localparam real CLKOUT3_PHASE_REG = CLKOUT3_PHASE;
  localparam [40:1] CLKOUT3_USE_FINE_PS_REG = CLKOUT3_USE_FINE_PS;
  localparam [40:1] CLKOUT4_CASCADE_REG = CLKOUT4_CASCADE;
  localparam [31:0] CLKOUT4_DIVIDE_REG = CLKOUT4_DIVIDE;
  localparam real CLKOUT4_DUTY_CYCLE_REG = CLKOUT4_DUTY_CYCLE;
  localparam real CLKOUT4_PHASE_REG = CLKOUT4_PHASE;
  localparam [40:1] CLKOUT4_USE_FINE_PS_REG = CLKOUT4_USE_FINE_PS;
  localparam [31:0] CLKOUT5_DIVIDE_REG = CLKOUT5_DIVIDE;
  localparam real CLKOUT5_DUTY_CYCLE_REG = CLKOUT5_DUTY_CYCLE;
  localparam real CLKOUT5_PHASE_REG = CLKOUT5_PHASE;
  localparam [40:1] CLKOUT5_USE_FINE_PS_REG = CLKOUT5_USE_FINE_PS;
  localparam [31:0] CLKOUT6_DIVIDE_REG = CLKOUT6_DIVIDE;
  localparam real CLKOUT6_DUTY_CYCLE_REG = CLKOUT6_DUTY_CYCLE;
  localparam real CLKOUT6_PHASE_REG = CLKOUT6_PHASE;
  localparam [40:1] CLKOUT6_USE_FINE_PS_REG = CLKOUT6_USE_FINE_PS;
  localparam real CLKPFD_FREQ_MAX_REG = CLKPFD_FREQ_MAX;
  localparam real CLKPFD_FREQ_MIN_REG = CLKPFD_FREQ_MIN;
  localparam [64:1] COMPENSATION_REG = COMPENSATION;
  localparam [31:0] DIVCLK_DIVIDE_REG = DIVCLK_DIVIDE;
  localparam [0:0] IS_CLKFBIN_INVERTED_REG = IS_CLKFBIN_INVERTED;
  localparam [0:0] IS_CLKIN1_INVERTED_REG = IS_CLKIN1_INVERTED;
  localparam [0:0] IS_CLKIN2_INVERTED_REG = IS_CLKIN2_INVERTED;
  localparam [0:0] IS_CLKINSEL_INVERTED_REG = IS_CLKINSEL_INVERTED;
  localparam [0:0] IS_PSEN_INVERTED_REG = IS_PSEN_INVERTED;
  localparam [0:0] IS_PSINCDEC_INVERTED_REG = IS_PSINCDEC_INVERTED;
  localparam [0:0] IS_PWRDWN_INVERTED_REG = IS_PWRDWN_INVERTED;
  localparam [0:0] IS_RST_INVERTED_REG = IS_RST_INVERTED;
  localparam real REF_JITTER1_REG = REF_JITTER1;
  localparam real REF_JITTER2_REG = REF_JITTER2;
  localparam [40:1] SS_EN_REG = SS_EN;
  localparam [88:1] SS_MODE_REG = SS_MODE;
  localparam [31:0] SS_MOD_PERIOD_REG = SS_MOD_PERIOD;
  localparam [40:1] STARTUP_WAIT_REG = STARTUP_WAIT;
  localparam real VCOCLK_FREQ_MAX_REG = VCOCLK_FREQ_MAX;
  localparam real VCOCLK_FREQ_MIN_REG = VCOCLK_FREQ_MIN;
`endif

`ifdef XIL_XECLIB
  wire [1:0] BANDWIDTH_BIN;
  wire [63:0] CLKFBOUT_MULT_F_BIN;
  wire [63:0] CLKFBOUT_PHASE_BIN;
  wire CLKFBOUT_USE_FINE_PS_BIN;
  wire [63:0] CLKIN1_PERIOD_BIN;
  wire [63:0] CLKIN2_PERIOD_BIN;
  wire [63:0] CLKIN_FREQ_MAX_BIN;
  wire [63:0] CLKIN_FREQ_MIN_BIN;
  wire [63:0] CLKOUT0_DIVIDE_F_BIN;
  wire [63:0] CLKOUT0_DUTY_CYCLE_BIN;
  wire [63:0] CLKOUT0_PHASE_BIN;
  wire CLKOUT0_USE_FINE_PS_BIN;
  wire [7:0] CLKOUT1_DIVIDE_BIN;
  wire [63:0] CLKOUT1_DUTY_CYCLE_BIN;
  wire [63:0] CLKOUT1_PHASE_BIN;
  wire CLKOUT1_USE_FINE_PS_BIN;
  wire [7:0] CLKOUT2_DIVIDE_BIN;
  wire [63:0] CLKOUT2_DUTY_CYCLE_BIN;
  wire [63:0] CLKOUT2_PHASE_BIN;
  wire CLKOUT2_USE_FINE_PS_BIN;
  wire [7:0] CLKOUT3_DIVIDE_BIN;
  wire [63:0] CLKOUT3_DUTY_CYCLE_BIN;
  wire [63:0] CLKOUT3_PHASE_BIN;
  wire CLKOUT3_USE_FINE_PS_BIN;
  wire CLKOUT4_CASCADE_BIN;
  wire [7:0] CLKOUT4_DIVIDE_BIN;
  wire [63:0] CLKOUT4_DUTY_CYCLE_BIN;
  wire [63:0] CLKOUT4_PHASE_BIN;
  wire CLKOUT4_USE_FINE_PS_BIN;
  wire [7:0] CLKOUT5_DIVIDE_BIN;
  wire [63:0] CLKOUT5_DUTY_CYCLE_BIN;
  wire [63:0] CLKOUT5_PHASE_BIN;
  wire CLKOUT5_USE_FINE_PS_BIN;
  wire [7:0] CLKOUT6_DIVIDE_BIN;
  wire [63:0] CLKOUT6_DUTY_CYCLE_BIN;
  wire [63:0] CLKOUT6_PHASE_BIN;
  wire CLKOUT6_USE_FINE_PS_BIN;
  wire [63:0] CLKPFD_FREQ_MAX_BIN;
  wire [63:0] CLKPFD_FREQ_MIN_BIN;
  wire [2:0] COMPENSATION_BIN;
  wire [6:0] DIVCLK_DIVIDE_BIN;
  wire [63:0] REF_JITTER1_BIN;
  wire [63:0] REF_JITTER2_BIN;
  wire SS_EN_BIN;
  wire [1:0] SS_MODE_BIN;
  wire [15:0] SS_MOD_PERIOD_BIN;
  wire STARTUP_WAIT_BIN;
  wire [63:0] VCOCLK_FREQ_MAX_BIN;
  wire [63:0] VCOCLK_FREQ_MIN_BIN;
`else
  reg [1:0] BANDWIDTH_BIN;
  reg [63:0] CLKFBOUT_MULT_F_BIN;
  reg [63:0] CLKFBOUT_PHASE_BIN;
  reg CLKFBOUT_USE_FINE_PS_BIN;
  reg [63:0] CLKIN1_PERIOD_BIN;
  reg [63:0] CLKIN2_PERIOD_BIN;
  reg [63:0] CLKIN_FREQ_MAX_BIN;
  reg [63:0] CLKIN_FREQ_MIN_BIN;
  reg [63:0] CLKOUT0_DIVIDE_F_BIN;
  reg [63:0] CLKOUT0_DUTY_CYCLE_BIN;
  reg [63:0] CLKOUT0_PHASE_BIN;
  reg CLKOUT0_USE_FINE_PS_BIN;
  reg [7:0] CLKOUT1_DIVIDE_BIN;
  reg [63:0] CLKOUT1_DUTY_CYCLE_BIN;
  reg [63:0] CLKOUT1_PHASE_BIN;
  reg CLKOUT1_USE_FINE_PS_BIN;
  reg [7:0] CLKOUT2_DIVIDE_BIN;
  reg [63:0] CLKOUT2_DUTY_CYCLE_BIN;
  reg [63:0] CLKOUT2_PHASE_BIN;
  reg CLKOUT2_USE_FINE_PS_BIN;
  reg [7:0] CLKOUT3_DIVIDE_BIN;
  reg [63:0] CLKOUT3_DUTY_CYCLE_BIN;
  reg [63:0] CLKOUT3_PHASE_BIN;
  reg CLKOUT3_USE_FINE_PS_BIN;
  reg CLKOUT4_CASCADE_BIN;
  reg [7:0] CLKOUT4_DIVIDE_BIN;
  reg [63:0] CLKOUT4_DUTY_CYCLE_BIN;
  reg [63:0] CLKOUT4_PHASE_BIN;
  reg CLKOUT4_USE_FINE_PS_BIN;
  reg [7:0] CLKOUT5_DIVIDE_BIN;
  reg [63:0] CLKOUT5_DUTY_CYCLE_BIN;
  reg [63:0] CLKOUT5_PHASE_BIN;
  reg CLKOUT5_USE_FINE_PS_BIN;
  reg [7:0] CLKOUT6_DIVIDE_BIN;
  reg [63:0] CLKOUT6_DUTY_CYCLE_BIN;
  reg [63:0] CLKOUT6_PHASE_BIN;
  reg CLKOUT6_USE_FINE_PS_BIN;
  reg [63:0] CLKPFD_FREQ_MAX_BIN;
  reg [63:0] CLKPFD_FREQ_MIN_BIN;
  reg [2:0] COMPENSATION_BIN;
  reg [6:0] DIVCLK_DIVIDE_BIN;
  reg [63:0] REF_JITTER1_BIN;
  reg [63:0] REF_JITTER2_BIN;
  reg SS_EN_BIN;
  reg [1:0] SS_MODE_BIN;
  reg [15:0] SS_MOD_PERIOD_BIN;
  reg STARTUP_WAIT_BIN;
  reg [63:0] VCOCLK_FREQ_MAX_BIN;
  reg [63:0] VCOCLK_FREQ_MIN_BIN;
`endif

  reg attr_test;
  reg attr_err;
  tri0 glblGSR = glbl.GSR;

  wire CDDCREQ_in;
  wire CLKFBIN_in;
  wire CLKIN1_in;
  wire CLKIN2_in;
  wire CLKINSEL_in;
  wire DCLK_in;
  wire DEN_in;
  wire DWE_in;
  wire PSCLK_in;
  wire PSEN_in;
  wire PSINCDEC_in;
  wire PWRDWN_in;
  wire RST_in;
  wire [15:0] DI_in;
  wire [6:0] DADDR_in;

`ifdef XIL_TIMING
  wire DCLK_delay;
  wire DEN_delay;
  wire DWE_delay;
  wire PSCLK_delay;
  wire PSEN_delay;
  wire PSINCDEC_delay;
  wire [15:0] DI_delay;
  wire [6:0] DADDR_delay;
`endif

`ifdef XIL_TIMING
  assign DADDR_in[0] = (DADDR[0] !== 1'bz) && DADDR_delay[0]; // rv 0
  assign DADDR_in[1] = (DADDR[1] !== 1'bz) && DADDR_delay[1]; // rv 0
  assign DADDR_in[2] = (DADDR[2] !== 1'bz) && DADDR_delay[2]; // rv 0
  assign DADDR_in[3] = (DADDR[3] !== 1'bz) && DADDR_delay[3]; // rv 0
  assign DADDR_in[4] = (DADDR[4] !== 1'bz) && DADDR_delay[4]; // rv 0
  assign DADDR_in[5] = (DADDR[5] !== 1'bz) && DADDR_delay[5]; // rv 0
  assign DADDR_in[6] = (DADDR[6] !== 1'bz) && DADDR_delay[6]; // rv 0
  assign DCLK_in = (DCLK !== 1'bz) && DCLK_delay; // rv 0
  assign DEN_in = (DEN !== 1'bz) && DEN_delay; // rv 0
  assign DI_in[0] = (DI[0] !== 1'bz) && DI_delay[0]; // rv 0
  assign DI_in[10] = (DI[10] !== 1'bz) && DI_delay[10]; // rv 0
  assign DI_in[11] = (DI[11] !== 1'bz) && DI_delay[11]; // rv 0
  assign DI_in[12] = (DI[12] !== 1'bz) && DI_delay[12]; // rv 0
  assign DI_in[13] = (DI[13] !== 1'bz) && DI_delay[13]; // rv 0
  assign DI_in[14] = (DI[14] !== 1'bz) && DI_delay[14]; // rv 0
  assign DI_in[15] = (DI[15] !== 1'bz) && DI_delay[15]; // rv 0
  assign DI_in[1] = (DI[1] !== 1'bz) && DI_delay[1]; // rv 0
  assign DI_in[2] = (DI[2] !== 1'bz) && DI_delay[2]; // rv 0
  assign DI_in[3] = (DI[3] !== 1'bz) && DI_delay[3]; // rv 0
  assign DI_in[4] = (DI[4] !== 1'bz) && DI_delay[4]; // rv 0
  assign DI_in[5] = (DI[5] !== 1'bz) && DI_delay[5]; // rv 0
  assign DI_in[6] = (DI[6] !== 1'bz) && DI_delay[6]; // rv 0
  assign DI_in[7] = (DI[7] !== 1'bz) && DI_delay[7]; // rv 0
  assign DI_in[8] = (DI[8] !== 1'bz) && DI_delay[8]; // rv 0
  assign DI_in[9] = (DI[9] !== 1'bz) && DI_delay[9]; // rv 0
  assign DWE_in = (DWE !== 1'bz) && DWE_delay; // rv 0
  assign PSCLK_in = (PSCLK !== 1'bz) && PSCLK_delay; // rv 0
  assign PSEN_in = (PSEN !== 1'bz) && (PSEN_delay ^ IS_PSEN_INVERTED_REG); // rv 0
  assign PSINCDEC_in = (PSINCDEC !== 1'bz) && (PSINCDEC_delay ^ IS_PSINCDEC_INVERTED_REG); // rv 0
`else
  assign DADDR_in[0] = (DADDR[0] !== 1'bz) && DADDR[0]; // rv 0
  assign DADDR_in[1] = (DADDR[1] !== 1'bz) && DADDR[1]; // rv 0
  assign DADDR_in[2] = (DADDR[2] !== 1'bz) && DADDR[2]; // rv 0
  assign DADDR_in[3] = (DADDR[3] !== 1'bz) && DADDR[3]; // rv 0
  assign DADDR_in[4] = (DADDR[4] !== 1'bz) && DADDR[4]; // rv 0
  assign DADDR_in[5] = (DADDR[5] !== 1'bz) && DADDR[5]; // rv 0
  assign DADDR_in[6] = (DADDR[6] !== 1'bz) && DADDR[6]; // rv 0
  assign DCLK_in = (DCLK !== 1'bz) && DCLK; // rv 0
  assign DEN_in = (DEN !== 1'bz) && DEN; // rv 0
  assign DI_in[0] = (DI[0] !== 1'bz) && DI[0]; // rv 0
  assign DI_in[10] = (DI[10] !== 1'bz) && DI[10]; // rv 0
  assign DI_in[11] = (DI[11] !== 1'bz) && DI[11]; // rv 0
  assign DI_in[12] = (DI[12] !== 1'bz) && DI[12]; // rv 0
  assign DI_in[13] = (DI[13] !== 1'bz) && DI[13]; // rv 0
  assign DI_in[14] = (DI[14] !== 1'bz) && DI[14]; // rv 0
  assign DI_in[15] = (DI[15] !== 1'bz) && DI[15]; // rv 0
  assign DI_in[1] = (DI[1] !== 1'bz) && DI[1]; // rv 0
  assign DI_in[2] = (DI[2] !== 1'bz) && DI[2]; // rv 0
  assign DI_in[3] = (DI[3] !== 1'bz) && DI[3]; // rv 0
  assign DI_in[4] = (DI[4] !== 1'bz) && DI[4]; // rv 0
  assign DI_in[5] = (DI[5] !== 1'bz) && DI[5]; // rv 0
  assign DI_in[6] = (DI[6] !== 1'bz) && DI[6]; // rv 0
  assign DI_in[7] = (DI[7] !== 1'bz) && DI[7]; // rv 0
  assign DI_in[8] = (DI[8] !== 1'bz) && DI[8]; // rv 0
  assign DI_in[9] = (DI[9] !== 1'bz) && DI[9]; // rv 0
  assign DWE_in = (DWE !== 1'bz) && DWE; // rv 0
  assign PSCLK_in = (PSCLK !== 1'bz) && PSCLK; // rv 0
  assign PSEN_in = (PSEN !== 1'bz) && (PSEN ^ IS_PSEN_INVERTED_REG); // rv 0
  assign PSINCDEC_in = (PSINCDEC !== 1'bz) && (PSINCDEC ^ IS_PSINCDEC_INVERTED_REG); // rv 0
`endif

  assign CDDCREQ_in = (CDDCREQ !== 1'bz) && CDDCREQ; // rv 0
  assign CLKFBIN_in = (CLKFBIN !== 1'bz) && (CLKFBIN ^ IS_CLKFBIN_INVERTED_REG); // rv 0
  assign CLKIN1_in = (CLKIN1 !== 1'bz) && (CLKIN1 ^ IS_CLKIN1_INVERTED_REG); // rv 0
  assign CLKIN2_in = (CLKIN2 !== 1'bz) && (CLKIN2 ^ IS_CLKIN2_INVERTED_REG); // rv 0
  assign CLKINSEL_in = (CLKINSEL === 1'bz) || (CLKINSEL ^ IS_CLKINSEL_INVERTED_REG); // rv 1
  assign PWRDWN_in = (PWRDWN !== 1'bz) && (PWRDWN ^ IS_PWRDWN_INVERTED_REG); // rv 0
  assign RST_in = (RST !== 1'bz) && (RST ^ IS_RST_INVERTED_REG); // rv 0

`ifndef XIL_XECLIB
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

`ifdef XIL_XECLIB
  assign BANDWIDTH_BIN =
    (BANDWIDTH_REG == "OPTIMIZED") ? BANDWIDTH_OPTIMIZED :
    (BANDWIDTH_REG == "HIGH") ? BANDWIDTH_HIGH :
    (BANDWIDTH_REG == "LOW") ? BANDWIDTH_LOW :
     BANDWIDTH_OPTIMIZED;

  assign CLKFBOUT_MULT_F_BIN = CLKFBOUT_MULT_F_REG * 1000;

  assign CLKFBOUT_PHASE_BIN = CLKFBOUT_PHASE_REG * 1000;

  assign CLKFBOUT_USE_FINE_PS_BIN =
    (CLKFBOUT_USE_FINE_PS_REG == "FALSE") ? CLKFBOUT_USE_FINE_PS_FALSE :
    (CLKFBOUT_USE_FINE_PS_REG == "TRUE") ? CLKFBOUT_USE_FINE_PS_TRUE :
     CLKFBOUT_USE_FINE_PS_FALSE;

  assign CLKIN1_PERIOD_BIN = CLKIN1_PERIOD_REG * 1000;

  assign CLKIN2_PERIOD_BIN = CLKIN2_PERIOD_REG * 1000;

  assign CLKIN_FREQ_MAX_BIN = CLKIN_FREQ_MAX_REG * 1000;

  assign CLKIN_FREQ_MIN_BIN = CLKIN_FREQ_MIN_REG * 1000;

  assign CLKOUT0_DIVIDE_F_BIN = CLKOUT0_DIVIDE_F_REG * 1000;

  assign CLKOUT0_DUTY_CYCLE_BIN = CLKOUT0_DUTY_CYCLE_REG * 1000;

  assign CLKOUT0_PHASE_BIN = CLKOUT0_PHASE_REG * 1000;

  assign CLKOUT0_USE_FINE_PS_BIN =
    (CLKOUT0_USE_FINE_PS_REG == "FALSE") ? CLKOUT0_USE_FINE_PS_FALSE :
    (CLKOUT0_USE_FINE_PS_REG == "TRUE") ? CLKOUT0_USE_FINE_PS_TRUE :
     CLKOUT0_USE_FINE_PS_FALSE;

  assign CLKOUT1_DIVIDE_BIN = CLKOUT1_DIVIDE_REG[7:0];

  assign CLKOUT1_DUTY_CYCLE_BIN = CLKOUT1_DUTY_CYCLE_REG * 1000;

  assign CLKOUT1_PHASE_BIN = CLKOUT1_PHASE_REG * 1000;

  assign CLKOUT1_USE_FINE_PS_BIN =
    (CLKOUT1_USE_FINE_PS_REG == "FALSE") ? CLKOUT1_USE_FINE_PS_FALSE :
    (CLKOUT1_USE_FINE_PS_REG == "TRUE") ? CLKOUT1_USE_FINE_PS_TRUE :
     CLKOUT1_USE_FINE_PS_FALSE;

  assign CLKOUT2_DIVIDE_BIN = CLKOUT2_DIVIDE_REG[7:0];

  assign CLKOUT2_DUTY_CYCLE_BIN = CLKOUT2_DUTY_CYCLE_REG * 1000;

  assign CLKOUT2_PHASE_BIN = CLKOUT2_PHASE_REG * 1000;

  assign CLKOUT2_USE_FINE_PS_BIN =
    (CLKOUT2_USE_FINE_PS_REG == "FALSE") ? CLKOUT2_USE_FINE_PS_FALSE :
    (CLKOUT2_USE_FINE_PS_REG == "TRUE") ? CLKOUT2_USE_FINE_PS_TRUE :
     CLKOUT2_USE_FINE_PS_FALSE;

  assign CLKOUT3_DIVIDE_BIN = CLKOUT3_DIVIDE_REG[7:0];

  assign CLKOUT3_DUTY_CYCLE_BIN = CLKOUT3_DUTY_CYCLE_REG * 1000;

  assign CLKOUT3_PHASE_BIN = CLKOUT3_PHASE_REG * 1000;

  assign CLKOUT3_USE_FINE_PS_BIN =
    (CLKOUT3_USE_FINE_PS_REG == "FALSE") ? CLKOUT3_USE_FINE_PS_FALSE :
    (CLKOUT3_USE_FINE_PS_REG == "TRUE") ? CLKOUT3_USE_FINE_PS_TRUE :
     CLKOUT3_USE_FINE_PS_FALSE;

  assign CLKOUT4_CASCADE_BIN =
    (CLKOUT4_CASCADE_REG == "FALSE") ? CLKOUT4_CASCADE_FALSE :
    (CLKOUT4_CASCADE_REG == "TRUE") ? CLKOUT4_CASCADE_TRUE :
     CLKOUT4_CASCADE_FALSE;

  assign CLKOUT4_DIVIDE_BIN = CLKOUT4_DIVIDE_REG[7:0];

  assign CLKOUT4_DUTY_CYCLE_BIN = CLKOUT4_DUTY_CYCLE_REG * 1000;

  assign CLKOUT4_PHASE_BIN = CLKOUT4_PHASE_REG * 1000;

  assign CLKOUT4_USE_FINE_PS_BIN =
    (CLKOUT4_USE_FINE_PS_REG == "FALSE") ? CLKOUT4_USE_FINE_PS_FALSE :
    (CLKOUT4_USE_FINE_PS_REG == "TRUE") ? CLKOUT4_USE_FINE_PS_TRUE :
     CLKOUT4_USE_FINE_PS_FALSE;

  assign CLKOUT5_DIVIDE_BIN = CLKOUT5_DIVIDE_REG[7:0];

  assign CLKOUT5_DUTY_CYCLE_BIN = CLKOUT5_DUTY_CYCLE_REG * 1000;

  assign CLKOUT5_PHASE_BIN = CLKOUT5_PHASE_REG * 1000;

  assign CLKOUT5_USE_FINE_PS_BIN =
    (CLKOUT5_USE_FINE_PS_REG == "FALSE") ? CLKOUT5_USE_FINE_PS_FALSE :
    (CLKOUT5_USE_FINE_PS_REG == "TRUE") ? CLKOUT5_USE_FINE_PS_TRUE :
     CLKOUT5_USE_FINE_PS_FALSE;

  assign CLKOUT6_DIVIDE_BIN = CLKOUT6_DIVIDE_REG[7:0];

  assign CLKOUT6_DUTY_CYCLE_BIN = CLKOUT6_DUTY_CYCLE_REG * 1000;

  assign CLKOUT6_PHASE_BIN = CLKOUT6_PHASE_REG * 1000;

  assign CLKOUT6_USE_FINE_PS_BIN =
    (CLKOUT6_USE_FINE_PS_REG == "FALSE") ? CLKOUT6_USE_FINE_PS_FALSE :
    (CLKOUT6_USE_FINE_PS_REG == "TRUE") ? CLKOUT6_USE_FINE_PS_TRUE :
     CLKOUT6_USE_FINE_PS_FALSE;

  assign CLKPFD_FREQ_MAX_BIN = CLKPFD_FREQ_MAX_REG * 1000;

  assign CLKPFD_FREQ_MIN_BIN = CLKPFD_FREQ_MIN_REG * 1000;

  assign COMPENSATION_BIN =
    (COMPENSATION_REG == "AUTO") ? COMPENSATION_AUTO :
    (COMPENSATION_REG == "BUF_IN") ? COMPENSATION_BUF_IN :
    (COMPENSATION_REG == "EXTERNAL") ? COMPENSATION_EXTERNAL :
    (COMPENSATION_REG == "INTERNAL") ? COMPENSATION_INTERNAL :
    (COMPENSATION_REG == "ZHOLD") ? COMPENSATION_ZHOLD :
     COMPENSATION_AUTO;

  assign DIVCLK_DIVIDE_BIN = DIVCLK_DIVIDE_REG[6:0];

  assign REF_JITTER1_BIN = REF_JITTER1_REG * 1000;

  assign REF_JITTER2_BIN = REF_JITTER2_REG * 1000;

  assign SS_EN_BIN =
    (SS_EN_REG == "FALSE") ? SS_EN_FALSE :
    (SS_EN_REG == "TRUE") ? SS_EN_TRUE :
     SS_EN_FALSE;

  assign SS_MODE_BIN =
    (SS_MODE_REG == "CENTER_HIGH") ? SS_MODE_CENTER_HIGH :
    (SS_MODE_REG == "CENTER_LOW") ? SS_MODE_CENTER_LOW :
    (SS_MODE_REG == "DOWN_HIGH") ? SS_MODE_DOWN_HIGH :
    (SS_MODE_REG == "DOWN_LOW") ? SS_MODE_DOWN_LOW :
     SS_MODE_CENTER_HIGH;

  assign SS_MOD_PERIOD_BIN = SS_MOD_PERIOD_REG[15:0];

  assign STARTUP_WAIT_BIN =
    (STARTUP_WAIT_REG == "FALSE") ? STARTUP_WAIT_FALSE :
    (STARTUP_WAIT_REG == "TRUE") ? STARTUP_WAIT_TRUE :
     STARTUP_WAIT_FALSE;

  assign VCOCLK_FREQ_MAX_BIN = VCOCLK_FREQ_MAX_REG * 1000;

  assign VCOCLK_FREQ_MIN_BIN = VCOCLK_FREQ_MIN_REG * 1000;

`else
  always @ (trig_attr) begin
  #1;
  BANDWIDTH_BIN =
      (BANDWIDTH_REG == "OPTIMIZED") ? BANDWIDTH_OPTIMIZED :
      (BANDWIDTH_REG == "HIGH") ? BANDWIDTH_HIGH :
      (BANDWIDTH_REG == "LOW") ? BANDWIDTH_LOW :
       BANDWIDTH_OPTIMIZED;
  
  CLKFBOUT_MULT_F_BIN = CLKFBOUT_MULT_F_REG * 1000;
  
  CLKFBOUT_PHASE_BIN = CLKFBOUT_PHASE_REG * 1000;
  
  CLKFBOUT_USE_FINE_PS_BIN =
      (CLKFBOUT_USE_FINE_PS_REG == "FALSE") ? CLKFBOUT_USE_FINE_PS_FALSE :
      (CLKFBOUT_USE_FINE_PS_REG == "TRUE") ? CLKFBOUT_USE_FINE_PS_TRUE :
       CLKFBOUT_USE_FINE_PS_FALSE;
  
  CLKIN1_PERIOD_BIN = CLKIN1_PERIOD_REG * 1000;
  
  CLKIN2_PERIOD_BIN = CLKIN2_PERIOD_REG * 1000;
  
  CLKIN_FREQ_MAX_BIN = CLKIN_FREQ_MAX_REG * 1000;
  
  CLKIN_FREQ_MIN_BIN = CLKIN_FREQ_MIN_REG * 1000;
  
  CLKOUT0_DIVIDE_F_BIN = CLKOUT0_DIVIDE_F_REG * 1000;
  
  CLKOUT0_DUTY_CYCLE_BIN = CLKOUT0_DUTY_CYCLE_REG * 1000;
  
  CLKOUT0_PHASE_BIN = CLKOUT0_PHASE_REG * 1000;
  
  CLKOUT0_USE_FINE_PS_BIN =
      (CLKOUT0_USE_FINE_PS_REG == "FALSE") ? CLKOUT0_USE_FINE_PS_FALSE :
      (CLKOUT0_USE_FINE_PS_REG == "TRUE") ? CLKOUT0_USE_FINE_PS_TRUE :
       CLKOUT0_USE_FINE_PS_FALSE;
  
  CLKOUT1_DIVIDE_BIN = CLKOUT1_DIVIDE_REG[7:0];
  
  CLKOUT1_DUTY_CYCLE_BIN = CLKOUT1_DUTY_CYCLE_REG * 1000;
  
  CLKOUT1_PHASE_BIN = CLKOUT1_PHASE_REG * 1000;
  
  CLKOUT1_USE_FINE_PS_BIN =
      (CLKOUT1_USE_FINE_PS_REG == "FALSE") ? CLKOUT1_USE_FINE_PS_FALSE :
      (CLKOUT1_USE_FINE_PS_REG == "TRUE") ? CLKOUT1_USE_FINE_PS_TRUE :
       CLKOUT1_USE_FINE_PS_FALSE;
  
  CLKOUT2_DIVIDE_BIN = CLKOUT2_DIVIDE_REG[7:0];
  
  CLKOUT2_DUTY_CYCLE_BIN = CLKOUT2_DUTY_CYCLE_REG * 1000;
  
  CLKOUT2_PHASE_BIN = CLKOUT2_PHASE_REG * 1000;
  
  CLKOUT2_USE_FINE_PS_BIN =
      (CLKOUT2_USE_FINE_PS_REG == "FALSE") ? CLKOUT2_USE_FINE_PS_FALSE :
      (CLKOUT2_USE_FINE_PS_REG == "TRUE") ? CLKOUT2_USE_FINE_PS_TRUE :
       CLKOUT2_USE_FINE_PS_FALSE;
  
  CLKOUT3_DIVIDE_BIN = CLKOUT3_DIVIDE_REG[7:0];
  
  CLKOUT3_DUTY_CYCLE_BIN = CLKOUT3_DUTY_CYCLE_REG * 1000;
  
  CLKOUT3_PHASE_BIN = CLKOUT3_PHASE_REG * 1000;
  
  CLKOUT3_USE_FINE_PS_BIN =
      (CLKOUT3_USE_FINE_PS_REG == "FALSE") ? CLKOUT3_USE_FINE_PS_FALSE :
      (CLKOUT3_USE_FINE_PS_REG == "TRUE") ? CLKOUT3_USE_FINE_PS_TRUE :
       CLKOUT3_USE_FINE_PS_FALSE;
  
  CLKOUT4_CASCADE_BIN =
      (CLKOUT4_CASCADE_REG == "FALSE") ? CLKOUT4_CASCADE_FALSE :
      (CLKOUT4_CASCADE_REG == "TRUE") ? CLKOUT4_CASCADE_TRUE :
       CLKOUT4_CASCADE_FALSE;
  
  CLKOUT4_DIVIDE_BIN = CLKOUT4_DIVIDE_REG[7:0];
  
  CLKOUT4_DUTY_CYCLE_BIN = CLKOUT4_DUTY_CYCLE_REG * 1000;
  
  CLKOUT4_PHASE_BIN = CLKOUT4_PHASE_REG * 1000;
  
  CLKOUT4_USE_FINE_PS_BIN =
      (CLKOUT4_USE_FINE_PS_REG == "FALSE") ? CLKOUT4_USE_FINE_PS_FALSE :
      (CLKOUT4_USE_FINE_PS_REG == "TRUE") ? CLKOUT4_USE_FINE_PS_TRUE :
       CLKOUT4_USE_FINE_PS_FALSE;
  
  CLKOUT5_DIVIDE_BIN = CLKOUT5_DIVIDE_REG[7:0];
  
  CLKOUT5_DUTY_CYCLE_BIN = CLKOUT5_DUTY_CYCLE_REG * 1000;
  
  CLKOUT5_PHASE_BIN = CLKOUT5_PHASE_REG * 1000;
  
  CLKOUT5_USE_FINE_PS_BIN =
      (CLKOUT5_USE_FINE_PS_REG == "FALSE") ? CLKOUT5_USE_FINE_PS_FALSE :
      (CLKOUT5_USE_FINE_PS_REG == "TRUE") ? CLKOUT5_USE_FINE_PS_TRUE :
       CLKOUT5_USE_FINE_PS_FALSE;
  
  CLKOUT6_DIVIDE_BIN = CLKOUT6_DIVIDE_REG[7:0];
  
  CLKOUT6_DUTY_CYCLE_BIN = CLKOUT6_DUTY_CYCLE_REG * 1000;
  
  CLKOUT6_PHASE_BIN = CLKOUT6_PHASE_REG * 1000;
  
  CLKOUT6_USE_FINE_PS_BIN =
      (CLKOUT6_USE_FINE_PS_REG == "FALSE") ? CLKOUT6_USE_FINE_PS_FALSE :
      (CLKOUT6_USE_FINE_PS_REG == "TRUE") ? CLKOUT6_USE_FINE_PS_TRUE :
       CLKOUT6_USE_FINE_PS_FALSE;
  
  CLKPFD_FREQ_MAX_BIN = CLKPFD_FREQ_MAX_REG * 1000;
  
  CLKPFD_FREQ_MIN_BIN = CLKPFD_FREQ_MIN_REG * 1000;
  
  COMPENSATION_BIN =
      (COMPENSATION_REG == "AUTO") ? COMPENSATION_AUTO :
      (COMPENSATION_REG == "BUF_IN") ? COMPENSATION_BUF_IN :
      (COMPENSATION_REG == "EXTERNAL") ? COMPENSATION_EXTERNAL :
      (COMPENSATION_REG == "INTERNAL") ? COMPENSATION_INTERNAL :
      (COMPENSATION_REG == "ZHOLD") ? COMPENSATION_ZHOLD :
       COMPENSATION_AUTO;
  
  DIVCLK_DIVIDE_BIN = DIVCLK_DIVIDE_REG[6:0];
  
  REF_JITTER1_BIN = REF_JITTER1_REG * 1000;
  
  REF_JITTER2_BIN = REF_JITTER2_REG * 1000;
  
  SS_EN_BIN =
      (SS_EN_REG == "FALSE") ? SS_EN_FALSE :
      (SS_EN_REG == "TRUE") ? SS_EN_TRUE :
       SS_EN_FALSE;
  
  SS_MODE_BIN =
      (SS_MODE_REG == "CENTER_HIGH") ? SS_MODE_CENTER_HIGH :
      (SS_MODE_REG == "CENTER_LOW") ? SS_MODE_CENTER_LOW :
      (SS_MODE_REG == "DOWN_HIGH") ? SS_MODE_DOWN_HIGH :
      (SS_MODE_REG == "DOWN_LOW") ? SS_MODE_DOWN_LOW :
       SS_MODE_CENTER_HIGH;
  
  SS_MOD_PERIOD_BIN = SS_MOD_PERIOD_REG[15:0];
  
  STARTUP_WAIT_BIN =
    (STARTUP_WAIT_REG == "FALSE") ? STARTUP_WAIT_FALSE :
    (STARTUP_WAIT_REG == "TRUE") ? STARTUP_WAIT_TRUE :
     STARTUP_WAIT_FALSE;

  VCOCLK_FREQ_MAX_BIN = VCOCLK_FREQ_MAX_REG * 1000;
  
  VCOCLK_FREQ_MIN_BIN = VCOCLK_FREQ_MIN_REG * 1000;
  
  end
`endif

`ifndef XIL_XECLIB
  always @ (trig_attr) begin
    #1;
    if ((attr_test == 1'b1) ||
        ((BANDWIDTH_REG != "OPTIMIZED") &&
         (BANDWIDTH_REG != "HIGH") &&
         (BANDWIDTH_REG != "LOW"))) begin
      $display("Error: [Unisim %s-101] BANDWIDTH attribute is set to %s.  Legal values for this attribute are OPTIMIZED, HIGH or LOW. Instance: %m", MODULE_NAME, BANDWIDTH_REG);
      attr_err = 1'b1;
    end

    if ((attr_test == 1'b1) ||
        (CLKFBOUT_MULT_F_REG < 2.000 || CLKFBOUT_MULT_F_REG > 128.000)) begin
      $display("Error: [Unisim %s-102] CLKFBOUT_MULT_F attribute is set to %f.  Legal values for this attribute are 2.000 to 128.000. Instance: %m", MODULE_NAME, CLKFBOUT_MULT_F_REG);
      attr_err = 1'b1;
    end

    if ((attr_test == 1'b1) ||
        (CLKFBOUT_PHASE_REG < -360.000 || CLKFBOUT_PHASE_REG > 360.000)) begin
      $display("Error: [Unisim %s-103] CLKFBOUT_PHASE attribute is set to %f.  Legal values for this attribute are -360.000 to 360.000. Instance: %m", MODULE_NAME, CLKFBOUT_PHASE_REG);
      attr_err = 1'b1;
    end

    if ((attr_test == 1'b1) ||
        ((CLKFBOUT_USE_FINE_PS_REG != "FALSE") &&
         (CLKFBOUT_USE_FINE_PS_REG != "TRUE"))) begin
      $display("Error: [Unisim %s-104] CLKFBOUT_USE_FINE_PS attribute is set to %s.  Legal values for this attribute are FALSE or TRUE. Instance: %m", MODULE_NAME, CLKFBOUT_USE_FINE_PS_REG);
      attr_err = 1'b1;
    end

    if ((attr_test == 1'b1) ||
        (CLKIN1_PERIOD_REG < 0.000 || CLKIN1_PERIOD_REG > 100.000)) begin
      $display("Error: [Unisim %s-105] CLKIN1_PERIOD attribute is set to %f.  Legal values for this attribute are 0.000 to 100.000. Instance: %m", MODULE_NAME, CLKIN1_PERIOD_REG);
      attr_err = 1'b1;
    end

    if ((attr_test == 1'b1) ||
        (CLKIN2_PERIOD_REG < 0.000 || CLKIN2_PERIOD_REG > 100.000)) begin
      $display("Error: [Unisim %s-106] CLKIN2_PERIOD attribute is set to %f.  Legal values for this attribute are 0.000 to 100.000. Instance: %m", MODULE_NAME, CLKIN2_PERIOD_REG);
      attr_err = 1'b1;
    end

    if ((attr_test == 1'b1) ||
        (CLKIN_FREQ_MAX_REG < 800.000 || CLKIN_FREQ_MAX_REG > 1066.000)) begin
      $display("Error: [Unisim %s-107] CLKIN_FREQ_MAX attribute is set to %f.  Legal values for this attribute are 800.000 to 1066.000. Instance: %m", MODULE_NAME, CLKIN_FREQ_MAX_REG);
      attr_err = 1'b1;
    end

    if ((attr_test == 1'b1) ||
        (CLKIN_FREQ_MIN_REG < 10.000 || CLKIN_FREQ_MIN_REG > 10.000)) begin
      $display("Error: [Unisim %s-108] CLKIN_FREQ_MIN attribute is set to %f.  Legal values for this attribute are 10.000 to 10.000. Instance: %m", MODULE_NAME, CLKIN_FREQ_MIN_REG);
      attr_err = 1'b1;
    end

    if ((attr_test == 1'b1) ||
        (CLKOUT0_DIVIDE_F_REG < 1.000 || CLKOUT0_DIVIDE_F_REG > 128.000)) begin
      $display("Error: [Unisim %s-109] CLKOUT0_DIVIDE_F attribute is set to %f.  Legal values for this attribute are 1.000 to 128.000. Instance: %m", MODULE_NAME, CLKOUT0_DIVIDE_F_REG);
      attr_err = 1'b1;
    end

    if ((attr_test == 1'b1) ||
        (CLKOUT0_DUTY_CYCLE_REG < 0.001 || CLKOUT0_DUTY_CYCLE_REG > 0.999)) begin
      $display("Error: [Unisim %s-110] CLKOUT0_DUTY_CYCLE attribute is set to %f.  Legal values for this attribute are 0.001 to 0.999. Instance: %m", MODULE_NAME, CLKOUT0_DUTY_CYCLE_REG);
      attr_err = 1'b1;
    end

    if ((attr_test == 1'b1) ||
        (CLKOUT0_PHASE_REG < -360.000 || CLKOUT0_PHASE_REG > 360.000)) begin
      $display("Error: [Unisim %s-111] CLKOUT0_PHASE attribute is set to %f.  Legal values for this attribute are -360.000 to 360.000. Instance: %m", MODULE_NAME, CLKOUT0_PHASE_REG);
      attr_err = 1'b1;
    end

    if ((attr_test == 1'b1) ||
        ((CLKOUT0_USE_FINE_PS_REG != "FALSE") &&
         (CLKOUT0_USE_FINE_PS_REG != "TRUE"))) begin
      $display("Error: [Unisim %s-112] CLKOUT0_USE_FINE_PS attribute is set to %s.  Legal values for this attribute are FALSE or TRUE. Instance: %m", MODULE_NAME, CLKOUT0_USE_FINE_PS_REG);
      attr_err = 1'b1;
    end

    if ((attr_test == 1'b1) ||
        ((CLKOUT1_DIVIDE_REG < 1) || (CLKOUT1_DIVIDE_REG > 128))) begin
      $display("Error: [Unisim %s-113] CLKOUT1_DIVIDE attribute is set to %d.  Legal values for this attribute are 1 to 128. Instance: %m", MODULE_NAME, CLKOUT1_DIVIDE_REG);
      attr_err = 1'b1;
    end

    if ((attr_test == 1'b1) ||
        (CLKOUT1_DUTY_CYCLE_REG < 0.001 || CLKOUT1_DUTY_CYCLE_REG > 0.999)) begin
      $display("Error: [Unisim %s-114] CLKOUT1_DUTY_CYCLE attribute is set to %f.  Legal values for this attribute are 0.001 to 0.999. Instance: %m", MODULE_NAME, CLKOUT1_DUTY_CYCLE_REG);
      attr_err = 1'b1;
    end

    if ((attr_test == 1'b1) ||
        (CLKOUT1_PHASE_REG < -360.000 || CLKOUT1_PHASE_REG > 360.000)) begin
      $display("Error: [Unisim %s-115] CLKOUT1_PHASE attribute is set to %f.  Legal values for this attribute are -360.000 to 360.000. Instance: %m", MODULE_NAME, CLKOUT1_PHASE_REG);
      attr_err = 1'b1;
    end

    if ((attr_test == 1'b1) ||
        ((CLKOUT1_USE_FINE_PS_REG != "FALSE") &&
         (CLKOUT1_USE_FINE_PS_REG != "TRUE"))) begin
      $display("Error: [Unisim %s-116] CLKOUT1_USE_FINE_PS attribute is set to %s.  Legal values for this attribute are FALSE or TRUE. Instance: %m", MODULE_NAME, CLKOUT1_USE_FINE_PS_REG);
      attr_err = 1'b1;
    end

    if ((attr_test == 1'b1) ||
        ((CLKOUT2_DIVIDE_REG < 1) || (CLKOUT2_DIVIDE_REG > 128))) begin
      $display("Error: [Unisim %s-117] CLKOUT2_DIVIDE attribute is set to %d.  Legal values for this attribute are 1 to 128. Instance: %m", MODULE_NAME, CLKOUT2_DIVIDE_REG);
      attr_err = 1'b1;
    end

    if ((attr_test == 1'b1) ||
        (CLKOUT2_DUTY_CYCLE_REG < 0.001 || CLKOUT2_DUTY_CYCLE_REG > 0.999)) begin
      $display("Error: [Unisim %s-118] CLKOUT2_DUTY_CYCLE attribute is set to %f.  Legal values for this attribute are 0.001 to 0.999. Instance: %m", MODULE_NAME, CLKOUT2_DUTY_CYCLE_REG);
      attr_err = 1'b1;
    end

    if ((attr_test == 1'b1) ||
        (CLKOUT2_PHASE_REG < -360.000 || CLKOUT2_PHASE_REG > 360.000)) begin
      $display("Error: [Unisim %s-119] CLKOUT2_PHASE attribute is set to %f.  Legal values for this attribute are -360.000 to 360.000. Instance: %m", MODULE_NAME, CLKOUT2_PHASE_REG);
      attr_err = 1'b1;
    end

    if ((attr_test == 1'b1) ||
        ((CLKOUT2_USE_FINE_PS_REG != "FALSE") &&
         (CLKOUT2_USE_FINE_PS_REG != "TRUE"))) begin
      $display("Error: [Unisim %s-120] CLKOUT2_USE_FINE_PS attribute is set to %s.  Legal values for this attribute are FALSE or TRUE. Instance: %m", MODULE_NAME, CLKOUT2_USE_FINE_PS_REG);
      attr_err = 1'b1;
    end

    if ((attr_test == 1'b1) ||
        ((CLKOUT3_DIVIDE_REG < 1) || (CLKOUT3_DIVIDE_REG > 128))) begin
      $display("Error: [Unisim %s-121] CLKOUT3_DIVIDE attribute is set to %d.  Legal values for this attribute are 1 to 128. Instance: %m", MODULE_NAME, CLKOUT3_DIVIDE_REG);
      attr_err = 1'b1;
    end

    if ((attr_test == 1'b1) ||
        (CLKOUT3_DUTY_CYCLE_REG < 0.001 || CLKOUT3_DUTY_CYCLE_REG > 0.999)) begin
      $display("Error: [Unisim %s-122] CLKOUT3_DUTY_CYCLE attribute is set to %f.  Legal values for this attribute are 0.001 to 0.999. Instance: %m", MODULE_NAME, CLKOUT3_DUTY_CYCLE_REG);
      attr_err = 1'b1;
    end

    if ((attr_test == 1'b1) ||
        (CLKOUT3_PHASE_REG < -360.000 || CLKOUT3_PHASE_REG > 360.000)) begin
      $display("Error: [Unisim %s-123] CLKOUT3_PHASE attribute is set to %f.  Legal values for this attribute are -360.000 to 360.000. Instance: %m", MODULE_NAME, CLKOUT3_PHASE_REG);
      attr_err = 1'b1;
    end

    if ((attr_test == 1'b1) ||
        ((CLKOUT3_USE_FINE_PS_REG != "FALSE") &&
         (CLKOUT3_USE_FINE_PS_REG != "TRUE"))) begin
      $display("Error: [Unisim %s-124] CLKOUT3_USE_FINE_PS attribute is set to %s.  Legal values for this attribute are FALSE or TRUE. Instance: %m", MODULE_NAME, CLKOUT3_USE_FINE_PS_REG);
      attr_err = 1'b1;
    end

    if ((attr_test == 1'b1) ||
        ((CLKOUT4_CASCADE_REG != "FALSE") &&
         (CLKOUT4_CASCADE_REG != "TRUE"))) begin
      $display("Error: [Unisim %s-125] CLKOUT4_CASCADE attribute is set to %s.  Legal values for this attribute are FALSE or TRUE. Instance: %m", MODULE_NAME, CLKOUT4_CASCADE_REG);
      attr_err = 1'b1;
    end

    if ((attr_test == 1'b1) ||
        ((CLKOUT4_DIVIDE_REG < 1) || (CLKOUT4_DIVIDE_REG > 128))) begin
      $display("Error: [Unisim %s-126] CLKOUT4_DIVIDE attribute is set to %d.  Legal values for this attribute are 1 to 128. Instance: %m", MODULE_NAME, CLKOUT4_DIVIDE_REG);
      attr_err = 1'b1;
    end

    if ((attr_test == 1'b1) ||
        (CLKOUT4_DUTY_CYCLE_REG < 0.001 || CLKOUT4_DUTY_CYCLE_REG > 0.999)) begin
      $display("Error: [Unisim %s-127] CLKOUT4_DUTY_CYCLE attribute is set to %f.  Legal values for this attribute are 0.001 to 0.999. Instance: %m", MODULE_NAME, CLKOUT4_DUTY_CYCLE_REG);
      attr_err = 1'b1;
    end

    if ((attr_test == 1'b1) ||
        (CLKOUT4_PHASE_REG < -360.000 || CLKOUT4_PHASE_REG > 360.000)) begin
      $display("Error: [Unisim %s-128] CLKOUT4_PHASE attribute is set to %f.  Legal values for this attribute are -360.000 to 360.000. Instance: %m", MODULE_NAME, CLKOUT4_PHASE_REG);
      attr_err = 1'b1;
    end

    if ((attr_test == 1'b1) ||
        ((CLKOUT4_USE_FINE_PS_REG != "FALSE") &&
         (CLKOUT4_USE_FINE_PS_REG != "TRUE"))) begin
      $display("Error: [Unisim %s-129] CLKOUT4_USE_FINE_PS attribute is set to %s.  Legal values for this attribute are FALSE or TRUE. Instance: %m", MODULE_NAME, CLKOUT4_USE_FINE_PS_REG);
      attr_err = 1'b1;
    end

    if ((attr_test == 1'b1) ||
        ((CLKOUT5_DIVIDE_REG < 1) || (CLKOUT5_DIVIDE_REG > 128))) begin
      $display("Error: [Unisim %s-130] CLKOUT5_DIVIDE attribute is set to %d.  Legal values for this attribute are 1 to 128. Instance: %m", MODULE_NAME, CLKOUT5_DIVIDE_REG);
      attr_err = 1'b1;
    end

    if ((attr_test == 1'b1) ||
        (CLKOUT5_DUTY_CYCLE_REG < 0.001 || CLKOUT5_DUTY_CYCLE_REG > 0.999)) begin
      $display("Error: [Unisim %s-131] CLKOUT5_DUTY_CYCLE attribute is set to %f.  Legal values for this attribute are 0.001 to 0.999. Instance: %m", MODULE_NAME, CLKOUT5_DUTY_CYCLE_REG);
      attr_err = 1'b1;
    end

    if ((attr_test == 1'b1) ||
        (CLKOUT5_PHASE_REG < -360.000 || CLKOUT5_PHASE_REG > 360.000)) begin
      $display("Error: [Unisim %s-132] CLKOUT5_PHASE attribute is set to %f.  Legal values for this attribute are -360.000 to 360.000. Instance: %m", MODULE_NAME, CLKOUT5_PHASE_REG);
      attr_err = 1'b1;
    end

    if ((attr_test == 1'b1) ||
        ((CLKOUT5_USE_FINE_PS_REG != "FALSE") &&
         (CLKOUT5_USE_FINE_PS_REG != "TRUE"))) begin
      $display("Error: [Unisim %s-133] CLKOUT5_USE_FINE_PS attribute is set to %s.  Legal values for this attribute are FALSE or TRUE. Instance: %m", MODULE_NAME, CLKOUT5_USE_FINE_PS_REG);
      attr_err = 1'b1;
    end

    if ((attr_test == 1'b1) ||
         ((CLKOUT6_DIVIDE_REG < 1) || (CLKOUT6_DIVIDE_REG > 128))) begin
      $display("Error: [Unisim %s-134] CLKOUT6_DIVIDE attribute is set to %d.  Legal values for this attribute are 1 to 128. Instance: %m", MODULE_NAME, CLKOUT6_DIVIDE_REG);
      attr_err = 1'b1;
    end

    if ((attr_test == 1'b1) ||
        (CLKOUT6_DUTY_CYCLE_REG < 0.001 || CLKOUT6_DUTY_CYCLE_REG > 0.999)) begin
      $display("Error: [Unisim %s-135] CLKOUT6_DUTY_CYCLE attribute is set to %f.  Legal values for this attribute are 0.001 to 0.999. Instance: %m", MODULE_NAME, CLKOUT6_DUTY_CYCLE_REG);
      attr_err = 1'b1;
    end

    if ((attr_test == 1'b1) ||
        (CLKOUT6_PHASE_REG < -360.000 || CLKOUT6_PHASE_REG > 360.000)) begin
      $display("Error: [Unisim %s-136] CLKOUT6_PHASE attribute is set to %f.  Legal values for this attribute are -360.000 to 360.000. Instance: %m", MODULE_NAME, CLKOUT6_PHASE_REG);
      attr_err = 1'b1;
    end

    if ((attr_test == 1'b1) ||
        ((CLKOUT6_USE_FINE_PS_REG != "FALSE") &&
         (CLKOUT6_USE_FINE_PS_REG != "TRUE"))) begin
      $display("Error: [Unisim %s-137] CLKOUT6_USE_FINE_PS attribute is set to %s.  Legal values for this attribute are FALSE or TRUE. Instance: %m", MODULE_NAME, CLKOUT6_USE_FINE_PS_REG);
      attr_err = 1'b1;
    end

    if ((attr_test == 1'b1) ||
        (CLKPFD_FREQ_MAX_REG < 450.000 || CLKPFD_FREQ_MAX_REG > 550.000)) begin
      $display("Error: [Unisim %s-138] CLKPFD_FREQ_MAX attribute is set to %f.  Legal values for this attribute are 450.000 to 550.000. Instance: %m", MODULE_NAME, CLKPFD_FREQ_MAX_REG);
      attr_err = 1'b1;
    end

    if ((attr_test == 1'b1) ||
        (CLKPFD_FREQ_MIN_REG < 10.000 || CLKPFD_FREQ_MIN_REG > 10.000)) begin
      $display("Error: [Unisim %s-139] CLKPFD_FREQ_MIN attribute is set to %f.  Legal values for this attribute are 10.000 to 10.000. Instance: %m", MODULE_NAME, CLKPFD_FREQ_MIN_REG);
      attr_err = 1'b1;
    end

    if ((attr_test == 1'b1) ||
        ((COMPENSATION_REG != "AUTO") &&
         (COMPENSATION_REG != "BUF_IN") &&
         (COMPENSATION_REG != "EXTERNAL") &&
         (COMPENSATION_REG != "INTERNAL") &&
         (COMPENSATION_REG != "ZHOLD"))) begin
      $display("Error: [Unisim %s-140] COMPENSATION attribute is set to %s.  Legal values for this attribute are AUTO, BUF_IN, EXTERNAL, INTERNAL or ZHOLD. Instance: %m", MODULE_NAME, COMPENSATION_REG);
      attr_err = 1'b1;
    end

    if ((attr_test == 1'b1) ||
         ((DIVCLK_DIVIDE_REG < 1) || (DIVCLK_DIVIDE_REG > 106))) begin
      $display("Error: [Unisim %s-141] DIVCLK_DIVIDE attribute is set to %d.  Legal values for this attribute are 1 to 106. Instance: %m", MODULE_NAME, DIVCLK_DIVIDE_REG);
      attr_err = 1'b1;
    end

    if ((attr_test == 1'b1) ||
        (REF_JITTER1_REG < 0.000 || REF_JITTER1_REG > 0.999)) begin
      $display("Error: [Unisim %s-150] REF_JITTER1 attribute is set to %f.  Legal values for this attribute are 0.000 to 0.999. Instance: %m", MODULE_NAME, REF_JITTER1_REG);
      attr_err = 1'b1;
    end

    if ((attr_test == 1'b1) ||
        (REF_JITTER2_REG < 0.000 || REF_JITTER2_REG > 0.999)) begin
      $display("Error: [Unisim %s-151] REF_JITTER2 attribute is set to %f.  Legal values for this attribute are 0.000 to 0.999. Instance: %m", MODULE_NAME, REF_JITTER2_REG);
      attr_err = 1'b1;
    end

    if ((attr_test == 1'b1) ||
        ((SS_EN_REG != "FALSE") &&
         (SS_EN_REG != "TRUE"))) begin
      $display("Error: [Unisim %s-152] SS_EN attribute is set to %s.  Legal values for this attribute are FALSE or TRUE. Instance: %m", MODULE_NAME, SS_EN_REG);
      attr_err = 1'b1;
    end

    if ((attr_test == 1'b1) ||
        ((SS_MODE_REG != "CENTER_HIGH") &&
         (SS_MODE_REG != "CENTER_LOW") &&
         (SS_MODE_REG != "DOWN_HIGH") &&
         (SS_MODE_REG != "DOWN_LOW"))) begin
      $display("Error: [Unisim %s-153] SS_MODE attribute is set to %s.  Legal values for this attribute are CENTER_HIGH, CENTER_LOW, DOWN_HIGH or DOWN_LOW. Instance: %m", MODULE_NAME, SS_MODE_REG);
      attr_err = 1'b1;
    end

    if ((attr_test == 1'b1) ||
        ((SS_MOD_PERIOD_REG < 4000) || (SS_MOD_PERIOD_REG > 40000))) begin
      $display("Error: [Unisim %s-154] SS_MOD_PERIOD attribute is set to %d.  Legal values for this attribute are 4000 to 40000. Instance: %m", MODULE_NAME, SS_MOD_PERIOD_REG);
      attr_err = 1'b1;
    end

    if ((attr_test == 1'b1) ||
        ((STARTUP_WAIT_REG != "FALSE") &&
         (STARTUP_WAIT_REG != "TRUE"))) begin
      $display("Error: [Unisim %s-155] STARTUP_WAIT attribute is set to %s.  Legal values for this attribute are FALSE or TRUE. Instance: %m", MODULE_NAME, STARTUP_WAIT_REG);
      attr_err = 1'b1;
    end

    if ((attr_test == 1'b1) ||
        (VCOCLK_FREQ_MAX_REG < 1600.000 || VCOCLK_FREQ_MAX_REG > 1600.000)) begin
      $display("Error: [Unisim %s-156] VCOCLK_FREQ_MAX attribute is set to %f.  Legal values for this attribute are 1600.000 to 1600.000. Instance: %m", MODULE_NAME, VCOCLK_FREQ_MAX_REG);
      attr_err = 1'b1;
    end

    if ((attr_test == 1'b1) ||
        (VCOCLK_FREQ_MIN_REG < 800.000 || VCOCLK_FREQ_MIN_REG > 800.000)) begin
      $display("Error: [Unisim %s-157] VCOCLK_FREQ_MIN attribute is set to %f.  Legal values for this attribute are 800.000 to 800.000. Instance: %m", MODULE_NAME, VCOCLK_FREQ_MIN_REG);
      attr_err = 1'b1;
    end

    if (attr_err == 1'b1) #1 $finish;
end
`endif

`ifdef XIL_TIMING
  reg notifier;
`endif

// begin behavioral model

  reg CDDCDONE_out;
  reg CLKFBOUTB_out;
  reg CLKFBOUT_out;
  reg CLKFBSTOPPED_out;
  reg CLKINSTOPPED_out;
  reg CLKOUT0B_out;
  reg CLKOUT0_out;
  reg CLKOUT1B_out;
  reg CLKOUT1_out;
  reg CLKOUT2B_out;
  reg CLKOUT2_out;
  reg CLKOUT3B_out;
  reg CLKOUT3_out;
  reg CLKOUT4_out;
  reg CLKOUT5_out;
  reg CLKOUT6_out;
  reg DRDY_out;
  reg LOCKED_out;
  reg PSDONE_out;
  reg [15:0] DO_out;

  assign CDDCDONE = CDDCDONE_out;
  assign CLKFBOUT = CLKFBOUT_out;
  assign CLKFBOUTB = CLKFBOUTB_out;
  assign CLKFBSTOPPED = CLKFBSTOPPED_out;
  assign CLKINSTOPPED = CLKINSTOPPED_out;
  assign CLKOUT0 =  CLKOUT0_out;
  assign CLKOUT0B =  CLKOUT0B_out;
  assign CLKOUT1 =  CLKOUT1_out;
  assign CLKOUT1B =  CLKOUT1B_out;
  assign CLKOUT2 =  CLKOUT2_out;
  assign CLKOUT2B =  CLKOUT2B_out;
  assign CLKOUT3 =  CLKOUT3_out;
  assign CLKOUT3B =  CLKOUT3B_out;
  assign CLKOUT4 =  CLKOUT4_out;
  assign CLKOUT5 =  CLKOUT5_out;
  assign CLKOUT6 =  CLKOUT6_out;
  assign DO = DO_out;
  assign DRDY = DRDY_out;
  assign LOCKED = LOCKED_out;
  assign PSDONE = PSDONE_out;

  localparam VCOCLK_FREQ_TARGET = 1000;
  localparam M_MIN = 2.000;
  localparam M_MAX = 128.000;
  localparam VF_MIN = 800.000;
  localparam D_MIN = 1;
  localparam D_MAX = 106;
  localparam O_MIN = 1;
  localparam O_MAX = 128;
  localparam O_MAX_HT_LT = 64;
  localparam REF_CLK_JITTER_MAX = 1000;
  localparam REF_CLK_JITTER_SCALE = 0.1;
  localparam MAX_FEEDBACK_DELAY = 5.0;
  localparam MAX_FEEDBACK_DELAY_SCALE = 1.0;
  localparam ps_max = 55;

  integer nBandwidth_HIGH=0;
  integer nBandwidth_LOW=1;
  integer nBandwidth_OPTIMIZED=2;

  reg [160:1] clkout_name;
  real CLKOUT0_DIVIDE_F_RND;
  real CLKFBOUT_MULT_F_RND;

  tri1 p_up;
  wire glock;

  integer pchk_tmp1, pchk_tmp2;
  integer clkvco_div_fint;
  real clkvco_div_frac;
  reg clk0_out;
  reg clkfbout_out;
  integer  clkvco_frac_en;
  integer ps_in_init;
  reg clk0_fps_en=0, clk1_fps_en=0, clk2_fps_en=0, clk3_fps_en=0;
  reg clk4_fps_en=0, clk5_fps_en=0, clk6_fps_en=0, clkfbout_fps_en=0;
  reg fps_en=1'b0, fps_clk_en=1'b0;
  reg clkinstopped_out1;
  reg  clkin_hold_f = 0;
  reg clkinstopped_out_dly2 = 0, clkin_stop_f = 0;
  integer  period_avg_stpi = 0,  period_avg_stp = 0;
  real tmp_stp1, tmp_stp2;
  reg pd_stp_p = 0;
  reg vco_stp_f = 0;
  reg  psen_w = 0;
  reg clkinstopped_out_dly = 0;
  reg clkfbin_stop_tmp, clkfbstopped_out1, clkin_stop_tmp;
  reg rst_clkinstopped = 0, rst_clkfbstopped = 0, rst_clkinstopped_tm = 0;
  reg rst_clkinstopped_rc = 0;
  reg rst_clkinstopped_lk, rst_clkfbstopped_lk;
  integer clkin_lost_cnt;
  integer clkfbin_lost_cnt;
  reg  clkinstopped_hold = 0;
  integer ps_in_ps, ps_cnt;
  integer ps_in_ps_neg, ps_cnt_neg;
  reg [6:0] daddr_lat;
  reg valid_daddr;
  reg drp_lock;
  integer drp_lock_lat = 4;
  integer drp_lock_lat_cnt;
  reg [15:0] dr_sram [127:0];
  reg [160:0] tmp_string;
  reg rst_int = 1'b0;
  reg pwron_int;
  wire rst_in_o;
  reg  clk1_out, clk2_out, clk3_out, clk4_out, clk5_out, clk6_out;
  reg clkout_en, clkout_en1, clkout_en0, clkout_en0_tmp, clkout_en0_tmp1;
  integer clkout_en_val, clkout_en_t;
  integer  clkin_lock_cnt;
  integer clkout_en_time, locked_en_time, lock_cnt_max;
  integer pll_lock_time, lock_period_time;
  reg clkvco = 1'b0;
  reg clkvco_lk_dly_tmp;
  reg clkvco_lk_en;
  reg clkvco_lk;
  reg fbclk_tmp;
  reg clkin_osc, clkin_p;
  reg clkfbin_osc, clkfbin_p;
  reg clkinstopped_vco_f;
  time rst_edge, rst_ht;
  reg fb_delay_found=1'b0, fb_delay_found_tmp=1'b0;
  reg clkfbout_tst=1'b0;
  real fb_delay_max;
  time fb_delay=0, clkvco_delay, val_tmp, dly_tmp, fb_comp_delay;
  time dly_tmp1, tmp_ps_val2;
  integer dly_tmp_int, tmp_ps_val1;
  time clkin_edge, delay_edge;
  real     period_clkin, clkin_period_tmp;
  integer  clkin_period_tmp_t;
  integer  clkin_period [4:0];
  integer  period_vco, period_vco_half, period_vco_half1, period_vco_half_rm;
  real     period_vco_rl, period_vco_rl_half;
  integer  period_vco_half_rm1, period_vco_half_rm2;
  real     cmpvco = 0.0;
  real     clkvco_pdrm;
  integer  period_vco_mf;
  integer  period_vco_tmp;
  integer  period_vco_rm, period_vco_cmp_cnt, clkvco_rm_cnt;
  integer  period_vco_cmp_flag;
  integer  period_vco_max, period_vco_min;
  integer  period_vco1, period_vco2, period_vco3, period_vco4;
  integer  period_vco5, period_vco6, period_vco7;
  integer  period_vco_target, period_vco_target_half;
  integer  period_fb=100000, period_avg=100000;
  integer  clk0_frac_lt, clk0_frac_ht;
  real     clk0_frac_lt_rl, clk0_frac_ht_rl;
  integer  clk0_frac_rm;
  real     clk0_frac_rm_rl;
  integer  clkfbout_frac_lt, clkfbout_frac_ht;
  real     clkfbout_frac_lt_rl, clkfbout_frac_ht_rl;
  integer  clkfbout_frac_rm;
  real     clkfbout_frac_rm_rl;
  integer period_ps, period_ps_old;
  reg  ps_lock, ps_lock_dly;
  real    clkvco_freq_init_chk, clkfbout_pm_rl;
  real    tmp_real;
  integer ik0, ik1, ik2, ik3, ik4, ib, i, j;
  integer md_product, m_product, m_product2;
  integer mf_product, clk0f_product;
//  integer clkin_lost_val, clkfbin_lost_val, clkin_lost_val_lk;
  integer clkin_lost_val;
  integer clkfbin_lost_val;
  time pll_locked_delay, clkin_dly_t, clkfbin_dly_t;
  wire pll_unlock, pll_unlock1;
  reg pll_locked_tmp1, pll_locked_tmp2;
  reg lock_period;
  reg pll_locked_tm, unlock_recover;
  reg clkpll_jitter_unlock;
  integer  clkin_jit, REF_CLK_JITTER_MAX_tmp;
  wire init_trig,  clkpll_r;
  reg clk0in=1'b0,clk1in=1'b0,clk2in=1'b0,clk3in=1'b0;
  reg clk4in=1'b0,clk5in=1'b0,clk6in=1'b0;
  reg clkpll_tmp1, clkpll;
  reg clkfboutin=1'b0;
  wire clkfbps_en;
  reg chk_ok;
  wire clk0ps_en, clk1ps_en, clk2ps_en, clk3ps_en;
  wire clk4ps_en, clk5ps_en, clk6ps_en;
  reg [3:0]  d_rsel, clkfbout_rsel, clk0_rsel;
  reg [3:0]  d_fsel, clkfbout_fsel, clk0_fsel;
  reg [6:0] d_fht, clkfbout_fht, clk0_fht;
  reg [6:0] d_flt, clkfbout_flt, clk0_flt;
  reg [5:0] clk0_dly_cnt;
  reg [5:0] clk1_dly_cnt;
  reg [5:0] clk2_dly_cnt;
  reg [5:0] clk3_dly_cnt;
  reg [5:0] clk4_dly_cnt;
  reg [5:0] clk5_dly_cnt;
  reg [5:0] clk6_dly_cnt;
  real clk0_phase, clk0_duty;
  real clk1_phase, clk1_duty;
  real clk2_phase, clk2_duty;
  real clk3_phase, clk3_duty;
  real clk4_phase, clk4_duty;
  real clk5_phase, clk5_duty;
  real clk6_phase, clk6_duty;
  real divclk_phase=0.000, divclk_duty=0.500;
  real clkfbout_phase, clkfbout_duty=0.500;
// mem cells
  reg [2:0] d_frac, clkfbout_frac, clk0_frac;
  reg  d_frac_en, clkfbout_frac_en, clk0_frac_en;
  reg clk0_cddc_en=1'b0, clk1_cddc_en=1'b0, clk2_cddc_en=1'b0, clk3_cddc_en=1'b0, clk4_cddc_en=1'b0, clk5_cddc_en=1'b0, clk6_cddc_en=1'b0, clkfbout_cddc_res=1'b0;
  reg  d_wf_f;
  reg  clkfbout_wf_f, clk0_wf_f;
  reg  d_wf_r;
  reg  clkfbout_wf_r, clk0_wf_r;
  reg [2:0] d_mx, clkfbout_mx;
  reg [2:0] clk0_mx, clk1_mx, clk2_mx, clk3_mx;
  reg [2:0] clk4_mx, clk5_mx, clk6_mx;
  reg divclk_e, clkfbin_e;
  reg clkfbout_e;
  reg clk0_e, clk1_e, clk2_e, clk3_e;
  reg clk4_e, clk5_e, clk6_e;
  reg divclk_nc, clkfbin_nc;
  reg clkfbout_nc;
  reg clk0_nc, clk1_nc, clk2_nc, clk3_nc;
  reg clk4_nc, clk5_nc, clk6_nc;
  reg [5:0] d_dt=0, clkfbout_dt=0;
  reg [5:0] clk0_dt=0, clk1_dt=0, clk2_dt=0, clk3_dt=0;
  reg [5:0] clk4_dt=0, clk5_dt=0, clk6_dt=0;
  reg [2:0] d_pm_f;
  reg [2:0] clkfbout_pm_f, clk0_pm_f;
  reg [2:0] clkfbout_pm_r, clk0_pm_r;
  reg [2:0] d_pm;
  reg [2:0] clk1_pm, clk2_pm, clk3_pm;
  reg [2:0] clk4_pm, clk5_pm, clk6_pm;
  reg       divclk_en=1, clkfbout_en=1;
  reg       clk0_en=1, clk1_en=1, clk2_en=1, clk3_en=1;
  reg       clk4_en=1, clk5_en=1, clk6_en=1;
  reg [5:0] clkfbin_ht;
  reg [5:0] clkfbout_ht;
  reg [7:0] divclk_ht;
  reg [5:0] clk0_ht, clk1_ht, clk2_ht, clk3_ht;
  reg [5:0] clk4_ht, clk5_ht, clk6_ht;
  reg [5:0] clkfbin_lt;
  reg [7:0] divclk_lt;
  reg [6:0] clkfbout_lt;
  reg [6:0] clk0_lt, clk1_lt, clk2_lt, clk3_lt;
  reg [6:0] clk4_lt, clk5_lt, clk6_lt;
//
  real clkfbout_f_div=1.0;
  real clk0_f_div;
  integer d_div, clkfbout_div, clk0_div;
  reg [5:0] clkfbout_dly_cnt;
  reg [7:0] clkfbout_cnt;
  reg [7:0] clk0_cnt;
  reg [7:0] clk1_cnt, clk1_div;
  reg [7:0] clk2_cnt, clk2_div;
  reg [7:0] clk3_cnt, clk3_div;
  reg [7:0] clk4_cnt, clk4_div;
  reg [7:0] clk5_cnt, clk5_div;
  reg [7:0] clk6_cnt, clk6_div;
  integer divclk_cnt_max, clkfbout_cnt_max;
  integer clk0_cnt_max, clk1_cnt_max, clk2_cnt_max, clk3_cnt_max;
  integer clk4_cnt_max, clk5_cnt_max, clk6_cnt_max;
  integer divclk_cnt_ht, clkfbout_cnt_ht;
  integer clk0_cnt_ht, clk1_cnt_ht, clk2_cnt_ht, clk3_cnt_ht;
  integer clk4_cnt_ht, clk5_cnt_ht, clk6_cnt_ht;
  reg [7:0]  divclk_div=8'b1, divclk_cnt=8'b0;
  reg       divclk_out, divclk_out_tmp;
  reg [3:0] pll_cp, pll_res;
  reg [1:0] pll_lfhf;
  reg [1:0] pll_cpres = 2'b01;
  reg [4:0] drp_lock_ref_dly;
  reg [4:0] drp_lock_fb_dly;
  reg [9:0] drp_lock_cnt;
  reg [9:0] drp_unlock_cnt;
  reg [9:0] drp_lock_sat_high;
  wire  clkinsel_tmp;
  real  clkin_chk_t1, clkin_chk_t2;
  real  clkin_chk_t1_r, clkin_chk_t2_r;
  integer   clkin_chk_t1_i, clkin_chk_t2_i;
  real    clkpfd_freq_init_chk;
  reg init_chk;
  reg rst_clkinsel_flag = 0;
  wire CLKFBIN_int;
  wire pwrdwn_in1;
  reg pwrdwn_in1_h = 0;
  reg rst_input_r_h = 0;
  reg pchk_clr = 0;
  reg psincdec_chg = 0;
  reg psincdec_chg_tmp = 0;
  wire rst_input;
  wire clkfbin_sel;
  reg vcoflag = 0;
  reg drp_updt = 1'b0;

  real halfperiod_sum = 0.0;
  integer halfperiod = 0;
  reg clkvco_free = 1'b0;
  integer ik10=0, ik11=0;

  reg input_jitter_warn_issued;

`ifndef XIL_XECLIB
  initial begin
    #1;
    if ($realtime == 0) begin
      $display ("Error: [Unisim %s-1] Simulator resolution is set to a value greater than 1 ps. ", MODULE_NAME);
      $display ("The simulator resolution must be set to 1ps or smaller. Instance %m");
      #1 $finish;
    end
  end
`endif

`ifndef XIL_XECLIB
  always @ (trig_attr) begin
    #1;
    if (CLKOUT0_DIVIDE_F_REG > 1.0000 && CLKOUT0_DIVIDE_F_REG < 2.0000) begin
      $display("Error: [Unisim %s-2] The Attribute CLKOUT0_DIVIDE_F is set to %f.  Values in range of greater than 1 and less than 2 are not allowed. Instance %m", MODULE_NAME, CLKOUT0_DIVIDE_F_REG);
    #1 $finish;
    end

    CLKOUT0_DIVIDE_F_RND = $itor($rtoi((CLKOUT0_DIVIDE_F_REG + 0.0625) * 8.0)) / 8.0;
    CLKFBOUT_MULT_F_RND = $itor($rtoi((CLKFBOUT_MULT_F_REG + 0.0625) * 8.0)) / 8.0;

    if (CLKFBOUT_MULT_F_RND < CLKFBOUT_MULT_F_REG) begin
        $display(" Warning [Unisim %s-35]: CLKFBOUT_MULT_F is not set to a resolution of .125 (%f) and is being rounded down to (%f). Instance %m ", MODULE_NAME, CLKFBOUT_MULT_F_REG, CLKFBOUT_MULT_F_RND);
    end
    else if (CLKFBOUT_MULT_F_RND > CLKFBOUT_MULT_F_REG) begin
        $display(" Warning: [Unisim %s-36]: CLKFBOUT_MULT_F is not set to a resolution of .125 (%f) and is being rounded up to (%f). Instance %m ", MODULE_NAME, CLKFBOUT_MULT_F_REG, CLKFBOUT_MULT_F_RND);
    end

    if (CLKOUT0_DIVIDE_F_RND < CLKOUT0_DIVIDE_F_REG) begin
        $display(" Warning: [Unisim %s-37]: CLKOUT0_DIVIDE_F is not set to a resolution of .125 (%f) and is being rounded down to (%f). Instance %m ", MODULE_NAME, CLKOUT0_DIVIDE_F_REG, CLKOUT0_DIVIDE_F_RND);
    end
    else if (CLKOUT0_DIVIDE_F_RND > CLKOUT0_DIVIDE_F_REG) begin
        $display(" Warning: [Unisim %s-38]: CLKOUT0_DIVIDE_F is not set to a resolution of .125 (%f) and is being rounded up to (%f). Instance %m ", MODULE_NAME, CLKOUT0_DIVIDE_F_REG, CLKOUT0_DIVIDE_F_RND);
    end

    clkfbout_f_div = CLKFBOUT_MULT_F_RND;
    attr_to_mc(clkfbout_pm_f, clkfbout_wf_f, clkfbout_frac, clkfbout_frac_en, clkfbout_wf_r, clkfbout_mx, clkfbout_e, clkfbout_nc, clkfbout_dt, clkfbout_pm_r, clkfbout_en, clkfbout_ht, clkfbout_lt, CLKFBOUT_MULT_F_REG, CLKFBOUT_PHASE_REG, clkfbout_duty);
    ht_calc(clkfbout_frac, clkfbout_frac_en, clkfbout_e, clkfbout_ht, clkfbout_lt, clkfbout_f_div, clkfbout_rsel, clkfbout_fsel, clkfbout_fht, clkfbout_flt, clkfbout_cnt_max, clkfbout_cnt_ht, clkfbout_div);
    clk0_f_div = CLKOUT0_DIVIDE_F_RND;
    attr_to_mc(clk0_pm_f, clk0_wf_f, clk0_frac, clk0_frac_en, clk0_wf_r, clk0_mx, clk0_e, clk0_nc, clk0_dt, clk0_pm_r, clk0_en, clk0_ht, clk0_lt, CLKOUT0_DIVIDE_F_REG, CLKOUT0_PHASE_REG, CLKOUT0_DUTY_CYCLE_REG);
    ht_calc(clk0_frac, clk0_frac_en, clk0_e, clk0_ht, clk0_lt, clk0_f_div, clk0_rsel, clk0_fsel, clk0_fht, clk0_flt, clk0_cnt_max, clk0_cnt_ht, clk0_div);

    clk1_div = CLKOUT1_DIVIDE_REG;
    attr_to_mc(d_pm_f, d_wf_f, d_frac, d_frac_en, d_wf_r, clk1_mx, clk1_e, clk1_nc, clk1_dt, clk1_pm, clk1_en, clk1_ht, clk1_lt, CLKOUT1_DIVIDE_REG, CLKOUT1_PHASE_REG, CLKOUT1_DUTY_CYCLE_REG);
    ht_calc(3'b0, 1'b0, clk1_e, clk1_ht, clk1_lt, clk1_div, d_rsel, d_fsel, d_fht, d_flt, clk1_cnt_max, clk1_cnt_ht, d_div);
    clk2_div = CLKOUT2_DIVIDE_REG;
    attr_to_mc(d_pm_f, d_wf_f, d_frac, d_frac_en, d_wf_r, clk2_mx, clk2_e, clk2_nc, clk2_dt, clk2_pm, clk2_en, clk2_ht, clk2_lt, CLKOUT2_DIVIDE_REG, CLKOUT2_PHASE_REG, CLKOUT2_DUTY_CYCLE_REG);
    ht_calc(3'b0, 1'b0, clk2_e, clk2_ht, clk2_lt, clk2_div, d_rsel, d_fsel, d_fht, d_flt, clk2_cnt_max, clk2_cnt_ht, d_div);
    clk3_div = CLKOUT3_DIVIDE_REG;
    attr_to_mc(d_pm_f, d_wf_f, d_frac, d_frac_en, d_wf_r, clk3_mx, clk3_e, clk3_nc, clk3_dt, clk3_pm, clk3_en, clk3_ht, clk3_lt, CLKOUT3_DIVIDE_REG, CLKOUT3_PHASE_REG, CLKOUT3_DUTY_CYCLE_REG);
    ht_calc(3'b0, 1'b0, clk3_e, clk3_ht, clk3_lt, clk3_div, d_rsel, d_fsel, d_fht, d_flt, clk3_cnt_max, clk3_cnt_ht, d_div);
    clk4_div = CLKOUT4_DIVIDE_REG;
    attr_to_mc(d_pm_f, d_wf_f, d_frac, d_frac_en, d_wf_r, clk4_mx, clk4_e, clk4_nc, clk4_dt, clk4_pm, clk4_en, clk4_ht, clk4_lt, CLKOUT4_DIVIDE_REG, CLKOUT4_PHASE_REG, CLKOUT4_DUTY_CYCLE_REG);
    ht_calc(3'b0, 1'b0, clk4_e, clk4_ht, clk4_lt, clk4_div, d_rsel, d_fsel, d_fht, d_flt, clk4_cnt_max, clk4_cnt_ht, d_div);
    clk5_div = CLKOUT5_DIVIDE_REG;
    attr_to_mc(d_pm_f, d_wf_f, d_frac, d_frac_en, d_wf_r, clk5_mx, clk5_e, clk5_nc, clk5_dt, clk5_pm, clk5_en, clk5_ht, clk5_lt, CLKOUT5_DIVIDE_REG, CLKOUT5_PHASE_REG, CLKOUT5_DUTY_CYCLE_REG);
    ht_calc(3'b0, 1'b0, clk5_e, clk5_ht, clk5_lt, clk5_div, d_rsel, d_fsel, d_fht, d_flt, clk5_cnt_max, clk5_cnt_ht, d_div);
    clk6_div = CLKOUT6_DIVIDE_REG;
    attr_to_mc(d_pm_f, d_wf_f, d_frac, d_frac_en, d_wf_r, clk6_mx, clk6_e, clk6_nc, clk6_dt, clk6_pm, clk6_en, clk6_ht, clk6_lt, CLKOUT6_DIVIDE_REG, CLKOUT6_PHASE_REG, CLKOUT6_DUTY_CYCLE_REG);
    ht_calc(3'b0, 1'b0, clk6_e, clk6_ht, clk6_lt, clk6_div, d_rsel, d_fsel, d_fht, d_flt, clk6_cnt_max, clk6_cnt_ht, d_div);
    divclk_div = DIVCLK_DIVIDE_REG;
    attr_to_mc(d_pm_f, d_wf_f, d_frac, d_frac_en, d_wf_r, d_mx, divclk_e, divclk_nc, d_dt, d_pm, divclk_en, divclk_ht, divclk_lt, DIVCLK_DIVIDE_REG, 0.000, 0.500);
    ht_calc(3'b0, 1'b0, divclk_e, divclk_ht, divclk_lt, divclk_div, d_rsel, d_fsel, d_fht, d_flt, divclk_cnt_max, divclk_cnt_ht, d_div);

    ps_in_init = 0;
    ps_in_ps = ps_in_init;
    ps_cnt = 0;

    clk0_fps_en = (CLKOUT0_USE_FINE_PS_REG == "TRUE");
    clk1_fps_en = (CLKOUT1_USE_FINE_PS_REG == "TRUE");
    clk2_fps_en = (CLKOUT2_USE_FINE_PS_REG == "TRUE");
    clk3_fps_en = (CLKOUT3_USE_FINE_PS_REG == "TRUE");
    clk4_fps_en = (CLKOUT4_USE_FINE_PS_REG == "TRUE");
    clk5_fps_en = (CLKOUT5_USE_FINE_PS_REG == "TRUE");
    clk6_fps_en = (CLKOUT6_USE_FINE_PS_REG == "TRUE");
    clkfbout_fps_en = (CLKFBOUT_USE_FINE_PS_REG == "TRUE");

    fps_en = clk0_fps_en || clk1_fps_en || clk2_fps_en || clk3_fps_en
             || clk4_fps_en || clk5_fps_en || clk6_fps_en || clkfbout_fps_en;

    if (clk0_frac_en == 1'b1) begin
      if (CLKOUT0_DUTY_CYCLE_REG != 0.5) begin
        $display("Error: [Unisim %s-3] The Attribute CLKOUT0_DUTY_CYCLE is set to %f.  This attribute should be set to 0.5 when CLKOUT0_DIVIDE_F has fraction part. Instance %m", MODULE_NAME, CLKOUT0_DUTY_CYCLE_REG);
        #1 $finish;
      end
    end

    pll_lfhf = 2'b00;

  if (BANDWIDTH_REG === "LOW")
    GetMultVal(clkfbout_div,nBandwidth_LOW,pll_cp,pll_res);
  else if (BANDWIDTH_REG === "HIGH")
    GetMultVal(clkfbout_div,nBandwidth_HIGH,pll_cp,pll_res);
  else if (BANDWIDTH_REG === "OPTIMIZED")
    GetMultVal(clkfbout_div,nBandwidth_OPTIMIZED,pll_cp,pll_res);

  GetLockDetSettings(clkfbout_div,drp_lock_ref_dly,drp_lock_fb_dly,drp_lock_cnt,drp_lock_sat_high,drp_unlock_cnt);

    tmp_string = "DIVCLK_DIVIDE";
    chk_ok = para_int_range_chk (DIVCLK_DIVIDE_REG, tmp_string, D_MIN, D_MAX);
      tmp_string = "CLKFBOUT_MULT_F";
      chk_ok = para_real_range_chk (CLKFBOUT_MULT_F_RND, tmp_string, M_MIN, M_MAX);
    tmp_string = "CLKOUT6_DUTY_CYCLE";
    chk_ok = clkout_duty_chk (CLKOUT6_DIVIDE_REG, CLKOUT6_DUTY_CYCLE_REG, tmp_string);
    if(clk0_frac_en == 1'b0) begin
      tmp_string = "CLKOUT0_DUTY_CYCLE";
      chk_ok = clkout_duty_chk (CLKOUT0_DIVIDE_F_RND, CLKOUT0_DUTY_CYCLE_REG, tmp_string);
    end
    tmp_string = "CLKOUT5_DUTY_CYCLE";
    chk_ok = clkout_duty_chk (CLKOUT5_DIVIDE_REG, CLKOUT5_DUTY_CYCLE_REG, tmp_string);
    tmp_string = "CLKOUT1_DUTY_CYCLE";
    chk_ok = clkout_duty_chk (CLKOUT1_DIVIDE_REG, CLKOUT1_DUTY_CYCLE_REG, tmp_string);
    tmp_string = "CLKOUT2_DUTY_CYCLE";
    chk_ok = clkout_duty_chk (CLKOUT2_DIVIDE_REG, CLKOUT2_DUTY_CYCLE_REG, tmp_string);
    tmp_string = "CLKOUT3_DUTY_CYCLE";
    chk_ok = clkout_duty_chk (CLKOUT3_DIVIDE_REG, CLKOUT3_DUTY_CYCLE_REG, tmp_string);
    tmp_string = "CLKOUT4_DUTY_CYCLE";
    chk_ok = clkout_duty_chk (CLKOUT4_DIVIDE_REG, CLKOUT4_DUTY_CYCLE_REG, tmp_string);
    period_vco_max = 1000000 / VCOCLK_FREQ_MIN_REG;
    period_vco_min = 1000000 / VCOCLK_FREQ_MAX_REG;
    period_vco_target = 1000000 / VCOCLK_FREQ_TARGET;
    period_vco_target_half = period_vco_target / 2;
    fb_delay_max = MAX_FEEDBACK_DELAY * MAX_FEEDBACK_DELAY_SCALE;
    clk0f_product = CLKOUT0_DIVIDE_F_RND * 8;
    pll_lock_time = 12;
    lock_period_time = 10;
    if (clkfbout_frac_en == 1'b1) begin
      md_product = clkfbout_div * DIVCLK_DIVIDE_REG;
      m_product = clkfbout_div;
      mf_product = CLKFBOUT_MULT_F_RND * 8;
      clkout_en_val = mf_product - 1;
      m_product2 = clkfbout_div / 2;
      clkout_en_time = mf_product + 4 + pll_lock_time;
      locked_en_time = md_product +  clkout_en_time + 2;
      lock_cnt_max = locked_en_time + 16;
    end
    else begin
      md_product = clkfbout_div * DIVCLK_DIVIDE_REG;
      m_product = clkfbout_div;
      mf_product = CLKFBOUT_MULT_F_RND * 8;
      m_product2 = clkfbout_div / 2;
      clkout_en_val = m_product;
      clkout_en_time = md_product + pll_lock_time;
      locked_en_time = md_product +  clkout_en_time + 2;
      lock_cnt_max = locked_en_time + 16;
    end
    REF_CLK_JITTER_MAX_tmp = REF_CLK_JITTER_MAX;
    ht_calc(clkfbout_frac, clkfbout_frac_en, clkfbout_e, clkfbout_ht, clkfbout_lt, clkfbout_f_div, clkfbout_rsel, clkfbout_fsel, clkfbout_fht, clkfbout_flt, clkfbout_cnt_max, clkfbout_cnt_ht, clkfbout_div);
    ht_calc(clk0_frac, clk0_frac_en, clk0_e, clk0_ht, clk0_lt, clk0_f_div, clk0_rsel, clk0_fsel, clk0_fht, clk0_flt, clk0_cnt_max, clk0_cnt_ht, clk0_div);
    divclk_div = DIVCLK_DIVIDE_REG;

    dr_sram[6] =  {clk5_pm[2:0], clk5_en, clk5_ht[5:0], clk5_lt[5:0]};
    dr_sram[7] =  {clk0_pm_f[2:0], clk0_wf_f, 1'bx, clk5_cddc_en,
                   2'b0, clk5_e, clk5_nc, clk5_dt[5:0]};
    dr_sram[8] =  {clk0_pm_r[2:0], clk0_en, clk0_ht[5:0], clk0_lt[5:0]};
    dr_sram[9] =  {clk0_cddc_en, clk0_frac[2:0], clk0_frac_en, clk0_wf_r,
                   2'b0, clk0_e, clk0_nc, clk0_dt[5:0]};
    dr_sram[10] = {clk1_pm[2:0], clk1_en, clk1_ht[5:0], clk1_lt[5:0]};
    dr_sram[11] = {5'bx, clk1_cddc_en, 2'b0, clk1_e, clk1_nc, clk1_dt[5:0]};
    dr_sram[12] = {clk2_pm[2:0], clk2_en, clk2_ht[5:0], clk2_lt[5:0]};
    dr_sram[13] = {5'bx, clk2_cddc_en, 2'b0, clk2_e, clk2_nc, clk2_dt[5:0]};
    dr_sram[14] = {clk3_pm[2:0], clk3_en, clk3_ht[5:0], clk3_lt[5:0]};
    dr_sram[15] = {5'bx, clk3_cddc_en, 2'b0, clk3_e, clk3_nc, clk3_dt[5:0]};
    dr_sram[16] = {clk4_pm[2:0], clk4_en, clk4_ht[5:0], clk4_lt[5:0]};
    dr_sram[17] = {5'bx, clk4_cddc_en, 2'b0, clk4_e, clk4_nc, clk4_dt[5:0]};
    dr_sram[18] = {clk6_pm[2:0], clk6_en, clk6_ht[5:0], clk6_lt[5:0]};
    dr_sram[19] = {clkfbout_pm_f[2:0], clkfbout_wf_f, 1'bx, clk6_cddc_en,
                   2'b0, clk6_e, clk6_nc, clk6_dt[5:0]};
    dr_sram[20] = {clkfbout_pm_r[2:0], clkfbout_en, clkfbout_ht[5:0], clkfbout_lt[5:0]};
    dr_sram[21] = {1'bx, clkfbout_frac[2:0], clkfbout_frac_en,
                   clkfbout_wf_r, 2'b0, clkfbout_e, clkfbout_nc, clkfbout_dt[5:0]};
    dr_sram[22] = {2'bx, divclk_e, divclk_nc, divclk_ht[5:0], divclk_lt[5:0]};
    dr_sram[23] = {2'bx, clkfbin_e, clkfbin_nc, clkfbin_ht[5:0], clkfbin_lt[5:0]};
    dr_sram[24] = {6'bx, drp_lock_cnt};
    dr_sram[25] = {1'bx, drp_lock_fb_dly, drp_unlock_cnt};
    dr_sram[26] = {1'bx, drp_lock_ref_dly, drp_lock_sat_high};
    dr_sram[28] = {11'bx, 5'b0};
    dr_sram[39] = {1'b1, 2'bx, 2'b11, 2'bx, 2'b11, 2'bx, 2'b11, 2'bx, 1'b1};
    dr_sram[78] = {pll_cp[3], 2'bx, pll_cp[2:1], 2'bx, pll_cp[0], 1'b0, 2'bx, pll_cpres, 3'bx};
    dr_sram[79] = {pll_res[3], 2'bx, pll_res[2:1], 2'bx, pll_res[0], pll_lfhf[1], 2'bx, pll_lfhf[0], 4'bx};
  end
`endif

  initial begin
    clkpll_jitter_unlock = 0;
    clkinstopped_vco_f = 0;
    rst_clkfbstopped = 0;
    rst_clkinstopped  = 0;
    rst_clkfbstopped_lk = 0;
    rst_clkinstopped_lk  = 0;
    clkfbin_stop_tmp = 0;
    clkin_stop_tmp = 0;
    clkvco_lk_en = 0;
    clkvco_lk_dly_tmp = 0;
    clkin_osc = 0;
    clkfbin_osc = 0;
    clkin_p = 0;
    clkfbin_p = 0;
    divclk_div = DIVCLK_DIVIDE_REG;
    ps_lock = 0;
    ps_lock_dly = 0;
    PSDONE_out = 1'b0;
    rst_int = 0;
    CLKINSTOPPED_out = 1'b0;
    clkinstopped_out1 = 0;
    CLKFBSTOPPED_out = 1'b0;
    clkfbstopped_out1 = 0;
    clkin_period[0] = 0;
    clkin_period[1] = 0;
    clkin_period[2] = 0;
    clkin_period[3] = 0;
    clkin_period[4] = 0;
    clkin_period_tmp_t = 0;
    period_avg = 100000;
    period_fb = 100000;
    clkin_lost_val = 2;
    clkfbin_lost_val = 2;
    fb_delay = 0;
    clkvco_delay = 0;
    val_tmp = 0;
    dly_tmp = 0;
    fb_comp_delay = 0;
    clkfbout_pm_rl = 0;
    period_vco = 0;
    period_vco1 = 0;
    period_vco2 = 0;
    period_vco3 = 0;
    period_vco4 = 0;
    period_vco5 = 0;
    period_vco6 = 0;
    period_vco7 = 0;
    period_vco_half = 0;
    period_vco_half1 = 0;
    period_vco_half_rm = 0;
    period_vco_half_rm1 = 0;
    period_vco_half_rm2 = 0;
    period_vco_rm = 0;
    period_vco_cmp_cnt = 0;
    period_vco_cmp_flag = 0;
    period_ps = 0;
    period_ps_old = 0;
    clkfbout_frac_ht = 0;
    clkfbout_frac_lt = 0;
    clk0_frac_ht = 0;
    clk0_frac_lt = 0;
    clk0_frac_ht_rl = 0.0;
    clk0_frac_lt_rl = 0.0;
    clkvco_rm_cnt = 0;
    fb_delay_found = 1'b0;
    fb_delay_found_tmp = 1'b0;
    clkin_edge = 0;
    delay_edge = 0;
    fbclk_tmp = 0;
    clkfbout_tst = 1'b0;
    clkout_en = 0;
    clkout_en0 = 0;
    clkout_en_t = 0;
    clkout_en0_tmp = 0;
    clkout_en1 = 0;
    pll_locked_tmp1  = 0;
    pll_locked_tmp2  = 0;
    pll_locked_tm = 0;
    pll_locked_delay = 0;
    unlock_recover = 0;
    clkin_jit = 0;
    clkin_lock_cnt = 0;
    lock_period = 0;
    rst_edge = 0;
    rst_ht = 0;
    DRDY_out = 1'b0;
    CDDCDONE_out = 1'b0;
    LOCKED_out = 1'b0;
    DO_out = 16'b0;
    drp_lock = 0;
    drp_lock_lat_cnt = 0;
    clk0_dly_cnt = 6'b0;
    clk1_dly_cnt = 6'b0;
    clk2_dly_cnt = 6'b0;
    clk3_dly_cnt = 6'b0;
    clk4_dly_cnt = 6'b0;
    clk5_dly_cnt = 6'b0;
    clk6_dly_cnt = 6'b0;
    clkfbout_dly_cnt = 6'b0;
    clk0_cnt = 8'b0;
    clk1_cnt = 8'b0;
    clk2_cnt = 8'b0;
    clk3_cnt = 8'b0;
    clk4_cnt = 8'b0;
    clk5_cnt = 8'b0;
    clk6_cnt = 8'b0;
    clkfbout_cnt = 8'b0;
    divclk_cnt = 8'b0;
    CLKOUT0_out = 1'b0;
    CLKOUT0B_out = 1'b1;
    CLKOUT1_out = 1'b0;
    CLKOUT1B_out = 1'b1;
    CLKOUT2_out = 1'b0;
    CLKOUT2B_out = 1'b1;
    CLKOUT3_out = 1'b0;
    CLKOUT3B_out = 1'b1;
    CLKOUT4_out = 1'b0;
    CLKOUT5_out = 1'b0;
    CLKOUT6_out = 1'b0;
    clk1_out = 0;
    clk2_out = 0;
    clk3_out = 0;
    clk4_out = 0;
    clk5_out = 0;
    clk6_out = 0;
    CLKFBOUT_out = 1'b0;
    CLKFBOUTB_out = 1'b1;
    divclk_out = 0;
    divclk_out_tmp = 0;
    clkin_osc = 0;
    clkfbin_osc = 0;
    clkin_p = 0;
    clkfbin_p = 0;
    pwron_int = 1;
    #100000 pwron_int = 0;
  end

  assign #2 clkinsel_tmp = CLKINSEL_in;

  assign  glock = (STARTUP_WAIT_BIN == STARTUP_WAIT_FALSE) || LOCKED;
  assign (weak1, strong0) glbl.PLL_LOCKG = (glock == 0) ? 0 : p_up;

  initial begin
    init_chk = 0;
    #2;
    init_chk = 1;
    #2;
    init_chk = 0;
  end

  always @(CLKINSEL_in or posedge init_chk ) begin
    #1;
    if (init_chk == 0 && $time > 3 && rst_int === 0 && (clkinsel_tmp === 0 || clkinsel_tmp === 1)) begin
      $display("Error: [Unisim %s-4] Input clock can only be switched when RST=1. CLKINSEL at time %t changed when RST=0. Instance %m", MODULE_NAME, $time);
      #1 $finish;
    end

    clkin_chk_t1_r = 1000.000 / CLKIN_FREQ_MIN_REG;
    clkin_chk_t1_i = $rtoi(1000.0 * clkin_chk_t1_r);
    clkin_chk_t1 = 0.001 * clkin_chk_t1_i;
    clkin_chk_t2_r = 1000.000 / CLKIN_FREQ_MAX_REG;
    clkin_chk_t2_i = $rtoi(1000.0 * clkin_chk_t2_r);
    clkin_chk_t2 = 0.001 * clkin_chk_t2_i;

    if (CLKINSEL_in === 1 && $time > 1 || CLKINSEL_in !== 0 && init_chk == 1) begin
      if (CLKIN1_PERIOD_REG * 1000 > clkin_chk_t1_i || CLKIN1_PERIOD_REG * 1000  < clkin_chk_t2_i) begin
        $display ("Error: [Unisim %s-5] The attribute CLKIN1_PERIOD is set to %f ns and out of the allowed range %f ns to %f ns set by CLKIN_FREQ_MIN/MAX. Instance %m", MODULE_NAME, CLKIN1_PERIOD_REG, clkin_chk_t2, clkin_chk_t1);

        #1 $finish;
      end
    end
    else if (CLKINSEL_in ===0 && $time > 1 || init_chk == 1 && clkinsel_tmp === 0 ) begin
      if (CLKIN2_PERIOD_REG * 1000 > clkin_chk_t1_i || CLKIN2_PERIOD_REG * 1000 < clkin_chk_t2_i) begin
        $display ("Error: [Unisim %s-6] The attribute CLKIN2_PERIOD is set to %f ns and out of the allowed range %f ns to %f ns set by CLKIN_FREQ_MIN/MAX. Instance %m", MODULE_NAME, CLKIN2_PERIOD_REG, clkin_chk_t2, clkin_chk_t1);
        #1 $finish;
      end
    end

    period_clkin =  (CLKINSEL_in === 0) ? CLKIN2_PERIOD_REG : CLKIN1_PERIOD_REG;
    if (period_clkin == 0) period_clkin = 10;

    if (period_clkin < MAX_FEEDBACK_DELAY)
      fb_delay_max = period_clkin * MAX_FEEDBACK_DELAY_SCALE;
    else
      fb_delay_max = MAX_FEEDBACK_DELAY * MAX_FEEDBACK_DELAY_SCALE;

    clkvco_freq_init_chk =  (1000.0 * CLKFBOUT_MULT_F_RND) / (period_clkin * DIVCLK_DIVIDE_REG);
   if (clkvco_freq_init_chk > VCOCLK_FREQ_MAX_REG || clkvco_freq_init_chk < VCOCLK_FREQ_MIN_REG) begin
     if (clkinsel_tmp === 0 && $time > 1 || clkinsel_tmp === 0 && init_chk === 1) begin
      $display ("Error: [Unisim %s-7] The calculated VCO frequency=%f Mhz. This exceeds the permitted VCO frequency range of %f Mhz to %f Mhz set by VCOCLK_FREQ_MIN/MAX. The VCO frequency is calculated with formula: VCO frequency =  CLKFBOUT_MULT_F / (DIVCLK_DIVIDE * CLKIN2_PERIOD). Please adjust the attributes to the permitted VCO frequency range. Instance %m", MODULE_NAME, clkvco_freq_init_chk, VCOCLK_FREQ_MIN_REG, VCOCLK_FREQ_MAX_REG);
      #1 $finish;
    end
    else if (clkinsel_tmp === 1 && $time > 1 || clkinsel_tmp !== 0 && init_chk === 1) begin
      $display ("Error: [Unisim %s-8] The calculated VCO frequency=%f Mhz. This exceeds the permitted VCO frequency range of %f Mhz to %f Mhz set by VCOCLK_FREQ_MIN/MAX. The VCO frequency is calculated with formula: VCO frequency =  CLKFBOUT_MULT_F / (DIVCLK_DIVIDE * CLKIN1_PERIOD). Please adjust the attributes to the permitted VCO frequency range. Instance %m", MODULE_NAME, clkvco_freq_init_chk, VCOCLK_FREQ_MIN_REG, VCOCLK_FREQ_MAX_REG);
      #1 $finish;
    end
   end
    clkpfd_freq_init_chk = (1000.0) / (period_clkin * DIVCLK_DIVIDE_REG);
   if (clkpfd_freq_init_chk > CLKPFD_FREQ_MAX_REG || clkpfd_freq_init_chk < CLKPFD_FREQ_MIN_REG) begin
     if (clkinsel_tmp === 0 && $time > 1 || clkinsel_tmp === 0 && init_chk === 1) begin
      $display ("Error: [Unisim %s-9] The calculated PFD frequency=%f Mhz. This exceeds the permitted PFD frequency range of %f Mhz to %f Mhz set by CLKPFD_FREQ_MIN/MAX. The PFD frequency is calculated with formula: PFD frequency =  1 /(DIVCLK_DIVIDE * CLKIN2_PERIOD). Please adjust the attributes to the permitted PFD frequency range. Instance %m", MODULE_NAME, clkpfd_freq_init_chk, CLKPFD_FREQ_MIN_REG, CLKPFD_FREQ_MAX_REG);
      #1 $finish;
    end
    else if (clkinsel_tmp === 1 && $time > 1 || clkinsel_tmp !== 0 && init_chk === 1) begin
      $display ("Error: [Unisim %s-10] The calculated PFD frequency=%f Mhz. This exceeds the permitted PFD frequency range of %f Mhz to %f Mhz set by CLKPFD_FREQ_MIN/MAX. The PFD frequency is calculated with formula: PFD frequency =  1 /(DIVCLK_DIVIDE * CLKIN1_PERIOD). Please adjust the attributes to the permitted PFD frequency range. Instance %m", MODULE_NAME, clkpfd_freq_init_chk, CLKPFD_FREQ_MIN_REG, CLKPFD_FREQ_MAX_REG);
      #1 $finish;
     end
   end
  end

  assign  init_trig = 1;
  assign clkpll_r = (CLKINSEL_in) ? CLKIN1_in : CLKIN2_in;
  assign pwrdwn_in1 =  (PWRDWN_in === 1) ? 1 : 0;
  assign rst_input  =  (RST_in === 1 | pwrdwn_in1 === 1) ? 1 : 0;

  always @(posedge clkpll_r or posedge rst_input)
    if (rst_input)
       rst_int <= 1;
    else
       rst_int <= rst_input ;

  assign rst_in_o = (rst_int || rst_clkfbstopped || rst_clkinstopped);

//simprim_rst_h
  always @(posedge pwrdwn_in1 or posedge pchk_clr)
    if (pwrdwn_in1)
       pwrdwn_in1_h <= 1;
    else if (pchk_clr)
       pwrdwn_in1_h <= 0;

  always @(posedge RST_in or posedge pchk_clr)
    if (RST_in)
       rst_input_r_h <= 1;
    else if (pchk_clr)
       rst_input_r_h <= 0;


  always @(rst_input )
    if (rst_input==1) begin
       rst_edge = $time;
       pchk_clr = 0;
    end
    else if (rst_input==0 && rst_edge > 1) begin
       rst_ht = $time - rst_edge;
       if (rst_ht < 1500)  begin
         if (rst_input_r_h == 1 && pwrdwn_in1_h == 1)
          $display("Warning: [Unisim %s-11] RST and PWRDWN at time %t must be asserted at least for 1.5 ns (actual %.3f ns) . Instance %m ", MODULE_NAME, $time, rst_ht/1000.0);
         else if (rst_input_r_h == 1 && pwrdwn_in1_h == 0)
          $display("Warning: [Unisim %s-12] RST at time %t must be asserted at least for 1.5 ns (actual %.3f ns). Instance %m", MODULE_NAME, $time, rst_ht/1000.0);
         else if (rst_input_r_h == 0 && pwrdwn_in1_h == 1)
          $display("Warning: [Unisim %s-13] PWRDWN at time %t must be asserted at least for 1.5 ns (actual %.3f ns). Instance %m", MODULE_NAME, $time, rst_ht/1000.0);
       end
       pchk_clr = 1;
    end
//endsimprim_rst_h

  //
  // DRP port read and write
  //

  always @ (*) begin
     DO_out = dr_sram[daddr_lat];
  end

  always @(posedge DCLK_in or posedge glblGSR)
    if (glblGSR == 1) begin
      drp_lock <= 0;
      drp_lock_lat_cnt <= 0;
      drp_updt <= 1'b0;
    end else begin
      if (~(RST_in || CDDCREQ_in) && drp_updt) drp_updt <= 1'b0;
      if (DEN_in == 1) begin
        valid_daddr = addr_is_valid(DADDR_in);
        if (drp_lock == 1) begin
          $display("Error: [Unisim %s-14] DEN is high at time %t. Need wait for DRDY signal before next read/write operation through DRP. Instance %m ", MODULE_NAME, $time);
        end else begin
          drp_lock <= 1;
          drp_lock_lat_cnt <= drp_lock_lat_cnt + 1;
          daddr_lat <= DADDR_in;
        end
        if (~valid_daddr) $display("Warning: [Unisim %s-15] Address DADDR=%b is unsupported at time %t. Instance %m ", MODULE_NAME, DADDR_in, $time);
        if (DWE_in == 1) begin          // write process
          if (rst_input == 1 || CDDCREQ_in == 1) begin
            if (valid_daddr) dr_sram[DADDR_in] <= DI_in;
            if (valid_daddr || drp_updt) drp_updt <= 1'b1;
            if (DADDR_in == 7'd6)
              lower_drp(clk5_pm, clk5_en, clk5_ht, clk5_lt, DI_in);
            else if (DADDR_in == 7'd7)
              upper_mix_drp(clk0_pm_f, clk0_wf_f, clk5_cddc_en, clk5_mx, clk5_e, clk5_nc, clk5_dt, DI_in);
            else if (DADDR_in == 7'd8)
              lower_drp(clk0_pm_r, clk0_en, clk0_ht, clk0_lt, DI_in);
            else if (DADDR_in == 7'd9) begin
              upper_frac_drp(clk0_cddc_en, clk0_frac, clk0_frac_en, clk0_wf_r, clk0_mx, clk0_e, clk0_nc, clk0_dt, DI_in);
            end else if (DADDR_in == 7'd10)
              lower_drp(clk1_pm, clk1_en, clk1_ht, clk1_lt, DI_in);
            else if (DADDR_in == 7'd11)
              upper_drp(clk1_cddc_en, clk1_mx, clk1_e, clk1_nc, clk1_dt, DI_in);
            else if (DADDR_in == 7'd12)
              lower_drp(clk2_pm, clk2_en, clk2_ht, clk2_lt, DI_in);
            else if (DADDR_in == 7'd13)
              upper_drp(clk2_cddc_en, clk2_mx, clk2_e, clk2_nc, clk2_dt, DI_in);
            else if (DADDR_in == 7'd14)
              lower_drp(clk3_pm, clk3_en, clk3_ht, clk3_lt, DI_in);
            else if (DADDR_in == 7'd15)
              upper_drp(clk3_cddc_en, clk3_mx, clk3_e, clk3_nc, clk3_dt, DI_in);
            else if (DADDR_in == 7'd16)
              lower_drp(clk4_pm, clk4_en, clk4_ht, clk4_lt, DI_in);
            else if (DADDR_in == 7'd17)
              upper_drp(clk4_cddc_en, clk4_mx, clk4_e, clk4_nc, clk4_dt, DI_in);
            else if (DADDR_in == 7'd18)
              lower_drp(clk6_pm, clk6_en, clk6_ht, clk6_lt, DI_in);
            else if (DADDR_in == 7'd19)
              upper_mix_drp(clkfbout_pm_f, clkfbout_wf_f, clk6_cddc_en, clk6_mx, clk6_e, clk6_nc, clk6_dt, DI_in);
            else if (DADDR_in == 7'd20)
              lower_drp(clkfbout_pm_r, clkfbout_en, clkfbout_ht, clkfbout_lt, DI_in);
            else if (DADDR_in == 7'd21)
              upper_frac_drp(clkfbout_cddc_res, clkfbout_frac, clkfbout_frac_en, clkfbout_wf_r, clkfbout_mx, clkfbout_e, clkfbout_nc, clkfbout_dt, DI_in);
            else if (DADDR_in == 7'd22) begin
               divclk_e = DI_in[13];
               divclk_nc = DI_in[12];
               divclk_ht = DI_in[11:6];
               divclk_lt = DI_in[5:0];
            end
            else if (DADDR_in == 7'd24)
              drp_lock_cnt = DI_in[9:0];
            else if (DADDR_in == 7'd25) begin
              drp_lock_fb_dly = DI_in[14:10];
              drp_unlock_cnt = DI_in[9:0];
            end
            else if (DADDR_in == 7'd26) begin
              drp_lock_ref_dly = DI_in[14:10];
              drp_lock_sat_high = DI_in[9:0];
            end
            else if (DADDR_in == 7'd78) 
              pll_cp = {DI_in[15],DI_in[12],DI_in[11],DI_in[8]};
            else if (DADDR_in == 7'd79)
              pll_res = {DI_in[15],DI_in[12],DI_in[11],DI_in[8]};
          end else begin
            $display("Error: [Unisim %s-18] RST is low at time %t. RST need to be high when changing paramters through DRP. Instance %m", MODULE_NAME, $time);
          end
        end //DWE
    end  //DEN
    if ( drp_lock == 1) begin
       if (drp_lock_lat_cnt < drp_lock_lat) begin
          drp_lock_lat_cnt <= drp_lock_lat_cnt + 1;
       end else begin
          drp_lock <= 0;
          DRDY_out <= 1;
          drp_lock_lat_cnt <= 0;
       end
    end
    if (DRDY == 1) DRDY_out <= 0;
  end

  always @(posedge CDDCREQ_in or negedge CDDCREQ_in)
  begin
    if (CDDCREQ_in == 1'b1)
     CDDCDONE_out <= 1'b0;
   else
   begin
     @(posedge clkvco)
     @(posedge clkvco)
     @(posedge clkvco)
     CDDCDONE_out <= ~CDDCREQ_in;
   end
  end

  function addr_is_valid;
  input [6:0] daddr_in;
  begin
    addr_is_valid = 1'b1;
    for (i=0; i<=6; i=i+1)
      if (daddr_in[i] != 0 && daddr_in[i] != 1) addr_is_valid = 1'b0;
    if ((addr_is_valid) &&
        ((daddr_in >= 7'd06 && daddr_in <= 7'd22) ||
         (daddr_in >= 7'd24 && daddr_in <= 7'd26) ||
         (daddr_in == 7'd28) ||
         (daddr_in == 7'd39) ||
         (daddr_in == 7'd78) ||
         (daddr_in == 7'd79))) addr_is_valid = 1'b1;
    else addr_is_valid = 1'b0;
  end
  endfunction

  // end process drp;

  //
  // determine clock period
  //

  always @(posedge clkpll_r or posedge rst_int or posedge rst_clkinsel_flag)
    if (rst_int || rst_clkinsel_flag)
    begin
      clkin_period[0] <= 1000 * period_clkin;
      clkin_period[1] <= 1000 * period_clkin;
      clkin_period[2] <= 1000 * period_clkin;
      clkin_period[3] <= 1000 * period_clkin;
      clkin_period[4] <= 1000 * period_clkin;
      clkin_jit <= 0;
      clkin_lock_cnt <= 0;
      pll_locked_tm <= 0;
      lock_period <= 0;
      pll_locked_tmp1 <= 0;
      clkout_en0_tmp <= 0;
      unlock_recover <= 0;
      clkin_edge <= 0;
    end else begin
      clkin_edge <= $time;
      if (clkin_edge != 0 && clkinstopped_out1 == 0 && rst_clkinsel_flag == 0) begin
         clkin_period[4] <= clkin_period[3];
         clkin_period[3] <= clkin_period[2];
         clkin_period[2] <= clkin_period[1];
         clkin_period[1] <= clkin_period[0];
         clkin_period[0] <= $time - clkin_edge;
      end

      if (pll_unlock == 0 && clkin_edge != 0 && clkinstopped_out1 == 0)
         clkin_jit <=  $time - clkin_edge - clkin_period[0];
      else
         clkin_jit <= 0;
      if ( ~glblGSR && (clkin_lock_cnt < lock_cnt_max) && fb_delay_found && pll_unlock1 == 0)
         clkin_lock_cnt <= clkin_lock_cnt + 1;
      else if (pll_unlock1 == 1 && pll_locked_tmp1 ==1 ) begin
         clkin_lock_cnt <= lock_cnt_max - 6;
         unlock_recover <= 1;
      end
      if ( clkin_lock_cnt >= pll_lock_time && pll_unlock1 == 0)
         pll_locked_tm <= #1 1;
      if ( clkin_lock_cnt == lock_period_time )
         lock_period <= 1;
      if (clkin_lock_cnt >= clkout_en_time && pll_locked_tm == 1) begin
         clkout_en0_tmp <= 1;
      end
      if (clkin_lock_cnt >= locked_en_time && clkout_en == 1)
         pll_locked_tmp1 <= 1;
      if (unlock_recover ==1 && clkin_lock_cnt  >= lock_cnt_max)
         unlock_recover <= 0;
    end

  always @(posedge pll_locked_tmp1)
    if (CLKINSEL_in === 0) begin
       pchk_tmp1 = CLKIN2_PERIOD_REG * 1100;
       pchk_tmp2 = CLKIN2_PERIOD_REG * 900;
       if (period_avg > pchk_tmp1 || period_avg < pchk_tmp2) begin
         $display("Warning: [Unisim %s-19] Input CLKIN2 period and attribute CLKIN2_PERIOD are not same. Instance %m ", MODULE_NAME);
       end
    end
    else begin
       pchk_tmp1 = CLKIN1_PERIOD_REG * 1100;
       pchk_tmp2 = CLKIN1_PERIOD_REG * 900;
       if (period_avg > pchk_tmp1 || period_avg < pchk_tmp2) begin
         $display("Warning: [Unisim %s-20] Input CLKIN1 period and attribute CLKIN1_PERIOD are not same. Instance %m ", MODULE_NAME);
       end
    end

  always @(*)
    if (rst_int == 0) begin
    if (clkfbout_frac_en == 1'b0) begin
      clkout_en_val = m_product;
      clkout_en_time = md_product + pll_lock_time;
      locked_en_time = md_product +  clkout_en_time + 2;
      lock_cnt_max = locked_en_time + 16;
    end
    else begin
      clkout_en_val = mf_product - 1;
      clkout_en_time = mf_product + 4 + pll_lock_time;
      locked_en_time = md_product +  clkout_en_time + 2;
      lock_cnt_max = locked_en_time + 16;
    end
    end

  always @(clkout_en0_tmp)
    clkout_en0_tmp1 <= #1 clkout_en0_tmp;

  always @(clkout_en0_tmp1 or clkout_en_t or clkout_en0_tmp )
    if (clkout_en0_tmp==0 )
      clkout_en0 = 0;
    else begin
     if (clkfbout_frac_en == 1'b1) begin
       if (clkout_en_t > clkout_en_val && clkout_en0_tmp1 == 1)
          clkout_en0 <= #period_vco6 clkout_en0_tmp1;
     end
     else begin
       if (clkout_en_t == clkout_en_val && clkout_en0_tmp1 == 1)
          clkout_en0 <= #period_vco6 clkout_en0_tmp1;
     end
   end

  always @(clkout_en0 )
    clkout_en1 <= #(clkvco_delay) clkout_en0;

  always @(clkout_en1 or rst_in_o )
  if (rst_in_o)
    clkout_en = 0;
  else
    clkout_en =  clkout_en1;

  always @(pll_locked_tmp1 )
    if (pll_locked_tmp1==0)
      pll_locked_tmp2 =  pll_locked_tmp1;
    else begin
      pll_locked_tmp2 <= #pll_locked_delay  pll_locked_tmp1;
    end

  always @(rst_int or glblGSR)
    if (rst_int || glblGSR) begin
      assign pll_locked_tmp2 = 0;
    end
    else begin
      deassign pll_locked_tmp2;
    end

  always @(rst_int)
    if (rst_int) begin
      assign clkout_en0 = 0;
      assign clkout_en1 = 0;
    end
    else begin
      deassign clkout_en0;
      deassign clkout_en1;
    end

  always @(rst_int or pll_locked_tm or pll_locked_tmp2 or pll_unlock or unlock_recover) begin
    if ((rst_int == 1) && (LOCKED !== 1'b0))
      LOCKED_out <= #1000 0;
    else if ((pll_locked_tm && pll_locked_tmp2 && ~pll_unlock && ~unlock_recover) === 1'b1)
      LOCKED_out <= 1'b1;
    else
      LOCKED_out <= 1'b0;
  end

  always @(clkin_period[0] or clkin_period[1] or clkin_period[2] or
           clkin_period[3] or clkin_period[4]) begin
    if (clkin_period[0] > clkin_period[1])
        clkin_period_tmp_t = clkin_period[0] - clkin_period[1];
    else
        clkin_period_tmp_t = clkin_period[1] - clkin_period[0];

    if ( ((clkin_period[0] > 0) && (clkin_period[0] != period_avg)) && (clkin_period[0] < 1.5 * period_avg || clkin_period_tmp_t <= 300) )
      period_avg = (clkin_period[0] + clkin_period[1] + clkin_period[2]
                 + clkin_period[3] + clkin_period[4])/5;
  end

  //CR-1062375
  always @(rst_int or LOCKED_out or clkin_period[4]) begin
    if(rst_int)
      input_jitter_warn_issued <= 1'b0;
    else if(LOCKED && !input_jitter_warn_issued)
      if(clkin_period[4]!=clkin_period[3]) begin
        $display("Warning: [Unisim %s-39] Input clock has jitter. This may cause misalignment in output clocks. Instance %m ", MODULE_NAME, $time);
        input_jitter_warn_issued <= 1'b1;
      end
  end

  always @(clkinstopped_out1 or clkin_hold_f or rst_int)
  if (rst_int)
     clkinstopped_hold = 0;
  else begin
    if (clkinstopped_out1)
      clkinstopped_hold <=  1;
    else begin
      if (clkin_hold_f)
         clkinstopped_hold = 0;
    end
  end

  always @(posedge clkinstopped_out1) begin
    period_avg_stpi <= period_avg;
    pd_stp_p <= #1 1;
    @(negedge clkvco)
     pd_stp_p <= #1 0;
  end

  always @(negedge clkvco or posedge rst_int or posedge pd_stp_p)
  if (rst_int) begin
    period_avg_stp <= 1000;
    vco_stp_f <= 0;
  end
  else if (pd_stp_p)
      period_avg_stp <=  period_avg_stpi;
  else  begin
    if (clkinstopped_out_dly2 == 1 && clkin_hold_f == 0) begin
      if (period_vco > 1739)
       vco_stp_f <= 1;
      else begin
         period_avg_stp  <= period_avg_stp + 1;
      end
    end
  end


  always @(period_avg or divclk_div or clkfbout_f_div or clkinstopped_hold
            or period_avg_stp or posedge rst_clkinstopped_rc)
  if (period_avg > 0 ) begin
    md_product = divclk_div * clkfbout_f_div;
    m_product = clkfbout_f_div;
    m_product2 = clkfbout_f_div / 2;
    clkvco_div_fint = $rtoi(clkfbout_f_div/divclk_div);
    clkvco_div_frac = (clkfbout_f_div/divclk_div) - clkvco_div_fint;
    if (clkvco_div_frac > 0.000)
    clkvco_frac_en = 1;
    else
    clkvco_frac_en = 0;
    period_fb = period_avg * divclk_div;
    period_vco_tmp = period_fb / clkfbout_f_div;
    period_vco_rl = 1.0 * period_fb / clkfbout_f_div;
    period_vco_rl_half = period_vco_rl / 2.0;
    clkvco_pdrm =  (period_avg * divclk_div / clkfbout_f_div) - period_vco_tmp;
    period_vco_mf = period_avg * 8;
    if (clkinstopped_hold == 1) begin
      if (clkin_hold_f) begin
        period_vco = (20000 * period_vco_tmp) / (20000 - period_vco_tmp);
        period_vco_rl = (20000 * period_vco_tmp) / (20000 - period_vco_tmp);
        period_vco_rl_half = period_vco_rl / 2.0;
      end
      else begin
        period_vco = period_avg_stp * divclk_div /clkfbout_f_div;
        period_vco_rl = period_avg_stp * divclk_div /clkfbout_f_div;
        period_vco_rl_half = period_vco_rl / 2.0;
      end
    end
    else
        period_vco = period_vco_tmp;

    period_vco_rm = period_fb % clkfbout_div;
    if (period_vco_rm > 1) begin
      if (period_vco_rm > m_product2)  begin
          period_vco_cmp_cnt = m_product / (m_product - period_vco_rm) - 1;
          period_vco_cmp_flag = 2;
      end
      else begin
         period_vco_cmp_cnt = (m_product / period_vco_rm) - 1;
         period_vco_cmp_flag = 1;
      end
    end
    else begin
      period_vco_cmp_cnt = 0;
      period_vco_cmp_flag = 0;
    end
    period_vco_half = period_vco /2;
    period_vco_half_rm = period_vco - period_vco_half;
    period_vco_half_rm1 = period_vco_half_rm + 1;
    if (period_vco_half_rm < 1)
      period_vco_half_rm2 = 0;
    else
      period_vco_half_rm2 = period_vco_half_rm - 1;
    period_vco_half1 = period_vco - period_vco_half + 1;
    pll_locked_delay = period_fb * clkfbout_f_div;
    clkin_dly_t =  period_avg * (divclk_div + 1.25);
    clkfbin_dly_t = period_fb * 2.25 ;
    period_vco1 = period_vco / 8;
    period_vco2 = period_vco / 4;
    period_vco3 = period_vco * 3/ 8;
    period_vco4 = period_vco / 2;
    period_vco5 = period_vco * 5 / 8;
    period_vco6 = period_vco *3 / 4;
    period_vco7 = period_vco * 7 / 8;
  end

  always @ (negedge RST_in or negedge CDDCREQ_in) begin
    if (drp_updt) begin
      clkout_name = "CLKFBOUT";
      mc_to_attr(clkout_name, clkfbout_pm_f, clkfbout_wf_f, clkfbout_frac, clkfbout_frac_en, clkfbout_wf_r, clkfbout_mx, clkfbout_e, clkfbout_nc, clkfbout_dt, clkfbout_pm_r, clkfbout_en, clkfbout_ht, clkfbout_lt, clkfbout_f_div, clkfbout_phase, clkfbout_duty);
      if (((clkfbout_f_div > M_MAX) || (clkfbout_f_div < M_MIN)) && ~clkfbout_nc)
        $display("Error : [Unisim %s-38] CLKFBOUT_MULT_F has been programmed through DRP to %f which is over the range of %f to %f. Instance %m at time %t.", MODULE_NAME, clkfbout_f_div, M_MIN, M_MAX, $time);
      check_m_settings(clkfbout_f_div,pll_cp,pll_res,drp_lock_ref_dly,drp_lock_fb_dly,drp_lock_cnt,drp_unlock_cnt,drp_lock_sat_high);
      #1;
      clkout_name = "CLKOUT0";
      mc_to_attr(clkout_name, clk0_pm_f, clk0_wf_f, clk0_frac, clk0_frac_en, clk0_wf_r, clk0_mx, clk0_e, clk0_nc, clk0_dt, clk0_pm_r, clk0_en, clk0_ht, clk0_lt, clk0_f_div, clk0_phase, clk0_duty);
      if (((clk0_f_div > O_MAX) || (clk0_f_div < O_MIN)) && ~clk0_nc)
        $display("Error : [Unisim %s-37] CLKOUT0_DIVIDE_F has been programmed through DRP to %f which is over the range of %d to %d. Instance %m at time %t.", MODULE_NAME, clk0_f_div, O_MIN, O_MAX, $time);
      #1;
      clkout_name = "CLKOUT1";
      mc_to_attr(clkout_name, 3'b0, 1'b0, 3'b0, 1'b0, 1'b0, clk1_mx, clk1_e, clk1_nc, clk1_dt, clk1_pm, clk1_en, clk1_ht, clk1_lt, clk1_div, clk1_phase, clk1_duty);
      clkout_name = "CLKOUT2";
      mc_to_attr(clkout_name, 3'b0, 1'b0, 3'b0, 1'b0, 1'b0, clk2_mx, clk2_e, clk2_nc, clk2_dt, clk2_pm, clk2_en, clk2_ht, clk2_lt, clk2_div, clk2_phase, clk2_duty);
      clkout_name = "CLKOUT3";
      mc_to_attr(clkout_name, 3'b0, 1'b0, 3'b0, 1'b0, 1'b0, clk3_mx, clk3_e, clk3_nc, clk3_dt, clk3_pm, clk3_en, clk3_ht, clk3_lt, clk3_div, clk3_phase, clk3_duty);
      clkout_name = "CLKOUT4";
      mc_to_attr(clkout_name, 3'b0, 1'b0, 3'b0, 1'b0, 1'b0, clk4_mx, clk4_e, clk4_nc, clk4_dt, clk4_pm, clk4_en, clk4_ht, clk4_lt, clk4_div, clk4_phase, clk4_duty);
      clkout_name = "CLKOUT5";
      mc_to_attr(clkout_name, 3'b0, 1'b0, 3'b0, 1'b0, 1'b0, clk5_mx, clk5_e, clk5_nc, clk5_dt, clk5_pm, clk5_en, clk5_ht, clk5_lt, clk5_div, clk5_phase, clk5_duty);
      clkout_name = "CLKOUT6";
      mc_to_attr(clkout_name, 3'b0, 1'b0, 3'b0, 1'b0, 1'b0, clk6_mx, clk6_e, clk6_nc, clk6_dt, clk6_pm, clk6_en, clk6_ht, clk6_lt, clk6_div, clk6_phase, clk6_duty);
      clkout_name = "DIVCLK";
      mc_to_attr(clkout_name, 3'b0, 1'b0, 3'b0, 1'b0, 1'b0, 2'b0, divclk_e, divclk_nc, 6'b0, 3'b0, divclk_en, divclk_ht, divclk_lt, divclk_div, divclk_phase, divclk_duty);
      if (((divclk_div > D_MAX) || (divclk_div < D_MIN)) && ~divclk_nc)
        $display("Error : [Unisim %s-34] DIVCLK_DIVIDE has been programmed through DRP to %f which is over the range of %d to %d at time %t. Instance %m", MODULE_NAME, divclk_div, D_MIN, D_MAX, $time);
      ht_calc(clkfbout_frac, clkfbout_frac_en, clkfbout_e, clkfbout_ht, clkfbout_lt, clkfbout_f_div, clkfbout_rsel, clkfbout_fsel, clkfbout_fht, clkfbout_flt, clkfbout_cnt_max, clkfbout_cnt_ht, clkfbout_div);
      ht_calc(clk0_frac, clk0_frac_en, clk0_e, clk0_ht, clk0_lt, clk0_f_div, clk0_rsel, clk0_fsel, clk0_fht, clk0_flt, clk0_cnt_max, clk0_cnt_ht, clk0_div);
      ht_calc(3'b0, 1'b0, clk1_e, clk1_ht, clk1_lt, clk1_div, d_rsel, d_fsel, d_fht, d_flt, clk1_cnt_max, clk1_cnt_ht, d_div);
      ht_calc(3'b0, 1'b0, clk2_e, clk2_ht, clk2_lt, clk2_div, d_rsel, d_fsel, d_fht, d_flt, clk2_cnt_max, clk2_cnt_ht, d_div);
      ht_calc(3'b0, 1'b0, clk3_e, clk3_ht, clk3_lt, clk3_div, d_rsel, d_fsel, d_fht, d_flt, clk3_cnt_max, clk3_cnt_ht, d_div);
      ht_calc(3'b0, 1'b0, clk4_e, clk4_ht, clk4_lt, clk4_div, d_rsel, d_fsel, d_fht, d_flt, clk4_cnt_max, clk4_cnt_ht, d_div);
      ht_calc(3'b0, 1'b0, clk5_e, clk5_ht, clk5_lt, clk5_div, d_rsel, d_fsel, d_fht, d_flt, clk5_cnt_max, clk5_cnt_ht, d_div);
      ht_calc(3'b0, 1'b0, clk6_e, clk6_ht, clk6_lt, clk6_div, d_rsel, d_fsel, d_fht, d_flt, clk6_cnt_max, clk6_cnt_ht, d_div);
      ht_calc(3'b0, 1'b0, divclk_e, divclk_ht, divclk_lt, divclk_div, d_rsel, d_fsel, d_fht, d_flt, divclk_cnt_max, divclk_cnt_ht, d_div);
    end
  end

  always @(clkfbout_f_div) begin
        mf_product = clkfbout_f_div * 8;
      end

  always @(*) begin
    if (clkfbout_frac_en) begin
      clkfbout_frac_ht_rl = period_vco_rl * clkfbout_fht + (period_vco_rl * clkfbout_rsel) / 8.0;
      clkfbout_frac_lt_rl = period_vco_rl * clkfbout_flt + (period_vco_rl * clkfbout_fsel) / 8.0;
      clkfbout_frac_ht = $rtoi(clkfbout_frac_ht_rl);
      clkfbout_frac_lt = $rtoi(clkfbout_frac_lt_rl);
    end
  end

  always @(*) begin
    if (clk0_frac_en) begin
      clk0_frac_ht_rl = period_vco_rl * clk0_fht + (period_vco_rl * clk0_rsel) / 8.0;
      clk0_frac_lt_rl = period_vco_rl * clk0_flt + (period_vco_rl * clk0_fsel) / 8.0;
      clk0_frac_ht = $rtoi(clk0_frac_ht_rl);
      clk0_frac_lt = $rtoi(clk0_frac_lt_rl);
    end
  end

  reg ps_wr_to_max = 1'b0;
  always @(period_vco or ps_in_ps)
  if (fps_en == 1) begin
    if (ps_in_ps < 0)
      period_ps = period_vco + ps_in_ps * period_vco / 56.0;
    else if ((ps_in_ps == 0) && PSINCDEC_in == 0)
      period_ps = 0;
    else
      period_ps = ps_in_ps * period_vco / 56.0;
  end


  always @( clkpll_r )
    clkpll_tmp1 <= #(period_avg) clkpll_r;

  always @(clkpll_tmp1)
    clkpll <= #(period_avg) clkpll_tmp1;

  always @(posedge clkinstopped_out1  or posedge rst_int)
  if ( rst_int)
      clkinstopped_vco_f <= 0;
  else begin
      clkinstopped_vco_f <= 1;
    @(negedge clkinstopped_out1 or posedge rst_int )
      if (rst_int)
      clkinstopped_vco_f <= 0;
      else begin
        @(posedge clkpll);
        @(posedge clkpll)
          clkinstopped_vco_f <= 0;
      end
   end

  always @(posedge clkinstopped_out1 or posedge rst_int)
    if (rst_int)
      CLKINSTOPPED_out <= 0;
    else begin
     CLKINSTOPPED_out <= 1;
     if (clkin_hold_f == 1) begin
        @(posedge LOCKED or posedge rst_int)
          CLKINSTOPPED_out <= 0;
     end
     else begin
       if (CLKINSEL_in == 1)
        $display("Warning: [Unisim %s-21] Input CLKIN1 is stopped at time %t. Reset is required when input clock returns. Instance %m ", MODULE_NAME, $time);
       else
        $display("Warning: [Unisim %s-22] Input CLKIN2 is stopped at time %t. Reset is required when input clock returns. Instance %m ", MODULE_NAME, $time);
     end
    end

  always @(posedge clkfbstopped_out1 or posedge rst_int)
  if (rst_int)
     CLKFBSTOPPED_out <= 1'b0;
  else begin
     CLKFBSTOPPED_out <= 1'b1;
     @(posedge LOCKED)
       CLKFBSTOPPED_out <= 1'b0;
  end

  always @(clkout_en_t)
    if (clkout_en_t >= clkout_en_val -3 && clkout_en_t < clkout_en_val)
        rst_clkinstopped_tm = 1;
    else
        rst_clkinstopped_tm =  0;

  always @(negedge clkinstopped_out1 or posedge rst_int)
    if (rst_int)
      rst_clkinstopped <= 0;
    else
     if (rst_clkinstopped_lk == 0 && clkin_hold_f == 1) begin
       @(posedge rst_clkinstopped_tm)
         rst_clkinstopped <= #period_vco4 1;
       @(negedge rst_clkinstopped_tm ) begin
         rst_clkinstopped <=  #period_vco5 0;
         rst_clkinstopped_rc <=  #period_vco6 1;
         rst_clkinstopped_rc <=  #period_vco7 0;
       end
      end

  always @(posedge clkinstopped_out1 or posedge rst_int)
    if (rst_int)
      clkinstopped_out_dly <= 0;
    else begin
       clkinstopped_out_dly <= 1;
       if (clkin_hold_f == 1) begin
         @(negedge rst_clkinstopped_rc or posedge rst_int)
           clkinstopped_out_dly <= 0;
       end
    end

  always @(clkinstopped_out1 or posedge rst_int)
    if (rst_int)
      clkinstopped_out_dly2 <= 0;
    else
       clkinstopped_out_dly2 <= clkinstopped_out1;

  always @(negedge rst_clkinstopped or posedge rst_int)
  if (rst_int)
     rst_clkinstopped_lk <= 0;
  else begin
      rst_clkinstopped_lk <= 1;
      @(posedge LOCKED)
        rst_clkinstopped_lk <= 0;
  end

  always @(clkinstopped_vco_f or  CLKINSTOPPED or clkvco_lk or clkvco_free or rst_int)
   if (rst_int)
     clkvco_lk  = 0;
   else begin
    if (CLKINSTOPPED == 1 && clkin_stop_f == 0)
      clkvco_lk <= #(period_vco_half) !clkvco_lk;
    else if (clkinstopped_vco_f == 1 && period_vco_half > 0)
       clkvco_lk <= #(period_vco_half) !clkvco_lk;
    else
      clkvco_lk  = clkvco_free;
   end

// free run vco comp

  always @(posedge clkpll) 
    if (pll_locked_tm == 1 ) begin
      clkvco_free = 1'b1;
      halfperiod_sum = 0.0;
      halfperiod = 0;
      if (clkfbout_frac_en == 1'b1 || clkvco_frac_en == 1) begin
        if (mf_product > 1) begin
          for (ik10=1; ik10 < mf_product; ik10=ik10+1) begin
            clkout_en_t <= ik10;
            halfperiod_sum = halfperiod_sum + period_vco_rl_half - halfperiod;
            halfperiod = $rtoi(halfperiod_sum);
            #halfperiod clkvco_free = 1'b0;
            halfperiod_sum = halfperiod_sum + period_vco_rl_half - halfperiod;
            halfperiod = $rtoi(halfperiod_sum);
            #halfperiod clkvco_free = 1'b1;
          end
          clkout_en_t <= ik10;
        end else begin
          clkout_en_t <= 1;
        end
      end else begin
        if (m_product > 1) begin
          for (ik11=1; ik11 < m_product; ik11=ik11+1) begin
            clkout_en_t <= ik11;
            halfperiod_sum = halfperiod_sum + period_vco_rl_half - halfperiod;
            halfperiod = $rtoi(halfperiod_sum);
            #halfperiod clkvco_free = 1'b0;
            halfperiod_sum = halfperiod_sum + period_vco_rl_half - halfperiod;
            halfperiod = $rtoi(halfperiod_sum);
            #halfperiod clkvco_free = 1'b1;
          end
          clkout_en_t <= ik11;
        end else begin
          clkout_en_t <= 1;
        end
      end
      halfperiod_sum = halfperiod_sum + period_vco_rl_half - halfperiod;
      halfperiod = $rtoi(halfperiod_sum);
      #halfperiod clkvco_free = 1'b0;
      if (clkfbout_f_div < divclk_div) begin
        #(period_vco_rl_half - period_avg/2.0);
      end
    end

  always @(fb_delay or period_vco or period_vco_mf or clkfbout_dt or clkfbout_pm_rl
         or lock_period or ps_in_ps )
   if (lock_period == 1) begin
     if (clkfbout_frac_en == 1'b1) begin
         val_tmp = period_avg * DIVCLK_DIVIDE_REG;
         fb_comp_delay = period_vco * (clkfbout_dt  + clkfbout_pm_rl);
     end
     else begin
        val_tmp = period_avg * DIVCLK_DIVIDE_REG;
        fb_comp_delay = period_vco * (clkfbout_dt  + clkfbout_pm_rl);
      end
    dly_tmp1 = fb_delay + fb_comp_delay;
    dly_tmp_int = 1;
    if (CLKFBOUT_USE_FINE_PS_BIN == CLKFBOUT_USE_FINE_PS_TRUE) begin
        if (ps_in_ps < 0) begin
           tmp_ps_val1 = -1 * ps_in_ps;
           tmp_ps_val2 = tmp_ps_val1 * period_vco / 56.0;
           if (tmp_ps_val2 > dly_tmp1 ) begin
             dly_tmp_int = -1;
             dly_tmp = tmp_ps_val2 - dly_tmp1;
           end
           else if (tmp_ps_val2 ==  dly_tmp1 ) begin
             dly_tmp_int = 0;
             dly_tmp = 0;
           end
           else begin
             dly_tmp_int = 1;
             dly_tmp =  dly_tmp1 - tmp_ps_val2;
           end
        end
        else
            dly_tmp = dly_tmp1 + ps_in_ps * period_vco / 56.0;
    end
    else
        dly_tmp = dly_tmp1;

    if (dly_tmp_int < 0)
      clkvco_delay = dly_tmp;
    else begin
       if (clkfbout_frac_en == 1'b1 && dly_tmp == 0)
          clkvco_delay = 0;
       else if ( dly_tmp < val_tmp)
          clkvco_delay = val_tmp - dly_tmp;
       else
          clkvco_delay = val_tmp - dly_tmp % val_tmp ;
    end
  end

  always @(clkfbout_pm_r)
    case (clkfbout_pm_r)
      3'b000 : clkfbout_pm_rl = 0.0;
      3'b001 : clkfbout_pm_rl = 0.125;
      3'b010 : clkfbout_pm_rl = 0.25;
      3'b011 : clkfbout_pm_rl = 0.375;
      3'b100 : clkfbout_pm_rl = 0.50;
      3'b101 : clkfbout_pm_rl = 0.625;
      3'b110 : clkfbout_pm_rl = 0.75;
      3'b111 : clkfbout_pm_rl = 0.875;
    endcase

  always @(clkvco_lk)
        clkvco_lk_dly_tmp <= #clkvco_delay clkvco_lk;

  always @(clkvco_lk_dly_tmp or clkvco_lk  or pll_locked_tm)
    if ( pll_locked_tm && vco_stp_f == 0) begin
      if (dly_tmp == 0)
         clkvco = clkvco_lk;
      else
         clkvco =  clkvco_lk_dly_tmp;
    end
    else
       clkvco = 0;

  always @(posedge PSCLK_in or posedge rst_int)
    if (rst_int) begin
      ps_in_ps <= ps_in_init;
      ps_cnt <= 0;
      psen_w <= 0;
      fps_clk_en <= 0;
      ps_lock <= 0;
    end else if (fps_en == 1) begin
     fps_clk_en <= 1;
     if (PSEN_in) begin
       if (psen_w == 1)
        $display("Error: [Unisim %s-23] PSEN is active more than 1 PSCLK period at time %t. PSEN must be active for only one PSCLK period. Instance %m ", MODULE_NAME, $time);

       psen_w <= 1;
       if (ps_lock == 1)
        $display("Warning: [Unisim %s-24] Please wait for PSDONE signal at time %t before adjusting the Phase Shift. Instance %m ", MODULE_NAME, $time);
       else if (PSINCDEC_in == 1) begin
           if (ps_cnt < ps_max)
              ps_cnt <= ps_cnt + 1;
           else
              ps_cnt <= 0;

           if (ps_in_ps < ps_max)
              ps_in_ps <= ps_in_ps + 1;
           else
              ps_in_ps <= 0;

           ps_lock <= 1;
       end
       else if (PSINCDEC_in == 0) begin
           ps_cnt_neg = (-1) * ps_cnt;
           ps_in_ps_neg = (-1) * ps_in_ps;
           if (ps_cnt_neg < ps_max)
              ps_cnt <= ps_cnt - 1;
           else
              ps_cnt <= 0;

           if (ps_in_ps_neg < ps_max)
              ps_in_ps <= ps_in_ps - 1;
           else
              ps_in_ps <= 0;

           ps_lock <= 1;
       end
     end
     else
        psen_w <= 0;

     if ( PSDONE == 1'b1)
            ps_lock <= 0;
  end

  always @(posedge ps_lock)
    if (fps_en == 1) begin
        @(posedge PSCLK_in)
        @(posedge PSCLK_in)
        @(posedge PSCLK_in)
        @(posedge PSCLK_in)
        @(posedge PSCLK_in)
        @(posedge PSCLK_in)
        @(posedge PSCLK_in)
        @(posedge PSCLK_in)
        @(posedge PSCLK_in)
        @(posedge PSCLK_in)
        @(posedge PSCLK_in)
          begin
            PSDONE_out = 1'b1;
            @(posedge PSCLK_in);
               PSDONE_out = 1'b0;
          end
  end

    always @(rst_clkinstopped)
    if (rst_clkinstopped) begin
      assign clkfbout_frac_ht = 50;
      assign clkfbout_frac_lt = 50;
      assign clkfbout_frac_ht_rl = 50.0;
      assign clkfbout_frac_lt_rl = 50.0;
    end
    else begin
      deassign clkfbout_frac_ht;
      deassign clkfbout_frac_lt;
      deassign clkfbout_frac_ht_rl;
      deassign clkfbout_frac_lt_rl;
    end

  integer clk0_delay, clk1_delay, clk2_delay, clk3_delay, clk4_delay, clk5_delay, clk6_delay, clkfbout_delay;
  integer clk0_delay_next, clk1_delay_next, clk2_delay_next, clk3_delay_next, clk4_delay_next, clk5_delay_next, clk6_delay_next, clkfbout_delay_next;
  always @(*) clk0_delay_next = clk0_pm_r*period_vco/8 + (clk0_fps_en*period_ps);
  always @(*) clk1_delay_next = clk1_pm*period_vco/8 + (clk1_fps_en*period_ps);
  always @(*) clk2_delay_next = clk2_pm*period_vco/8 + (clk2_fps_en*period_ps);
  always @(*) clk3_delay_next = clk3_pm*period_vco/8 + (clk3_fps_en*period_ps);
  always @(*) clk4_delay_next = clk4_pm*period_vco/8 + (clk4_fps_en*period_ps);
  always @(*) clk5_delay_next = clk5_pm*period_vco/8 + (clk5_fps_en*period_ps);
  always @(*) clk6_delay_next = clk6_pm*period_vco/8 + (clk6_fps_en*period_ps);
  always @(*) clkfbout_delay_next = clkfbout_pm_r*period_vco/8 + (clkfbout_fps_en*period_ps);

  always @ (posedge clkvco) begin
    if (ps_lock) begin
      if ((period_ps - period_ps_old) > period_vco/2)
        ps_wr_to_max <= 1'b1;
      else
        ps_wr_to_max <= 1'b0;
    end
    period_ps_old = period_ps;
    clk0_delay <= clk0_delay_next;
    clk1_delay <= clk1_delay_next;
    clk2_delay <= clk2_delay_next;
    clk3_delay <= clk3_delay_next;
    clk4_delay <= clk4_delay_next;
    clk5_delay <= clk5_delay_next;
    clk6_delay <= clk6_delay_next;
    clkfbout_delay <= clkfbout_delay_next;
  end

  always @ (clkvco) begin
    if (clkout_en && clk0_en)
      if (clk0_delay == 0) clk0in = clkvco;
      else if (clk0_fps_en && ps_wr_to_max && ~clkvco) begin
        clk0in <= #(clk0_delay - period_ps) 1'b0;
        clk0in <= #((2 * clk0_delay - period_ps)/2) 1'b1;
        clk0in <= #(clk0_delay) 1'b0;
      end else begin
        clk0in <= #clk0_delay clkvco;
      end
    else clk0in = 1'b0;
  end

  always @ (clkvco) begin
    if (clkout_en && clk1_en)
      if (clk1_delay == 0) clk1in = clkvco;
      else if (clk1_fps_en && ps_wr_to_max && ~clkvco) begin
        clk1in <= #(clk1_delay - period_ps) 1'b0;
        clk1in <= #((2 * clk1_delay - period_ps)/2) 1'b1;
        clk1in <= #(clk1_delay) 1'b0;
      end else begin
        clk1in <= #clk1_delay clkvco;
      end
    else clk1in = 1'b0;
  end

  always @ (clkvco) begin
    if (clkout_en && clk2_en)
      if (clk2_delay == 0) clk2in = clkvco;
      else if (clk2_fps_en && ps_wr_to_max && ~clkvco) begin
        clk2in <= #(clk2_delay - period_ps) 1'b0;
        clk2in <= #((2 * clk2_delay - period_ps)/2) 1'b1;
        clk2in <= #(clk2_delay) 1'b0;
      end else begin
        clk2in <= #clk2_delay clkvco;
      end
    else clk2in = 1'b0;
  end

  always @ (clkvco) begin
    if (clkout_en && clk3_en)
      if (clk3_delay == 0) clk3in = clkvco;
      else if (clk3_fps_en && ps_wr_to_max && ~clkvco) begin
        clk3in <= #(clk3_delay - period_ps) 1'b0;
        clk3in <= #((2 * clk3_delay - period_ps)/2) 1'b1;
        clk3in <= #(clk3_delay) 1'b0;
      end else begin
        clk3in <= #clk3_delay clkvco;
      end
    else clk3in = 1'b0;
  end

  always @ (clkvco) begin
    if (clkout_en && clk4_en)
      if (CLKOUT4_CASCADE_BIN == CLKOUT4_CASCADE_TRUE) clk4in = clk6_out;
      else if (clk4_delay == 0) clk4in = clkvco;
      else if (clk4_fps_en && ps_wr_to_max && ~clkvco) begin
        clk4in <= #(clk4_delay - period_ps) 1'b0;
        clk4in <= #((2 * clk4_delay - period_ps)/2) 1'b1;
        clk4in <= #(clk4_delay) 1'b0;
      end else begin
        clk4in <= #clk4_delay clkvco;
      end
    else clk4in = 1'b0;
  end

  always @ (clkvco) begin
    if (clkout_en && clk5_en)
      if (clk5_delay == 0) clk5in = clkvco;
      else if (clk5_fps_en && ps_wr_to_max && ~clkvco) begin
        clk5in <= #(clk5_delay - period_ps) 1'b0;
        clk5in <= #((2 * clk5_delay - period_ps)/2) 1'b1;
        clk5in <= #(clk5_delay) 1'b0;
      end else begin
        clk5in <= #clk5_delay clkvco;
      end
    else clk5in = 1'b0;
  end

  always @ (clkvco) begin
    if (clkout_en && clk6_en)
      if (clk6_delay == 0) clk6in = clkvco;
      else if (clk6_fps_en && ps_wr_to_max && ~clkvco) begin
        clk6in <= #(clk6_delay - period_ps) 1'b0;
        clk6in <= #((2 * clk6_delay - period_ps)/2) 1'b1;
        clk6in <= #(clk6_delay) 1'b0;
      end else begin
        clk6in <= #clk6_delay clkvco;
      end
    else clk6in = 1'b0;
  end

  always @ (clkvco) begin
    if (clkout_en && clkfbout_en)
      if (clkfbout_delay == 0) clkfboutin = clkvco;
      else if (clkfbout_fps_en && ps_wr_to_max && ~clkvco) begin
        clkfboutin <= #(clkfbout_delay - period_ps) 1'b0;
        clkfboutin <= #((2 * clkfbout_delay - period_ps)/2) 1'b1;
        clkfboutin <= #(clkfbout_delay) 1'b0;
      end else begin
        clkfboutin <= #clkfbout_delay clkvco;
      end
    else clkfboutin = 1'b0;
  end


  assign clk0ps_en = (clk0_dly_cnt == clk0_dt) & clkout_en;
  assign clk1ps_en = (clk1_dly_cnt == clk1_dt) & clkout_en;
  assign clk2ps_en = (clk2_dly_cnt == clk2_dt) & clkout_en;
  assign clk3ps_en = (clk3_dly_cnt == clk3_dt) & clkout_en;
  assign clk4ps_en = (clk4_dly_cnt == clk4_dt) & clkout_en;
  assign clk5ps_en = (clk5_dly_cnt == clk5_dt) & clkout_en;
  assign clk6ps_en = (clk6_dly_cnt == clk6_dt) & clkout_en;
  assign clkfbps_en = (clkfbout_dly_cnt == clkfbout_dt) & clkout_en;

 always  @(negedge clk0in or posedge rst_in_o)
   if (rst_in_o)
     clk0_dly_cnt <= 6'b0;
   else if (clkout_en == 1 ) begin
     if (clk0_dly_cnt < clk0_dt)
       clk0_dly_cnt <= clk0_dly_cnt + 1;
   end

  always  @(negedge clk1in or posedge rst_in_o)
    if (rst_in_o)
      clk1_dly_cnt <= 6'b0;
    else
      if (clk1_dly_cnt < clk1_dt && clkout_en ==1)
        clk1_dly_cnt <= clk1_dly_cnt + 1;

  always  @(negedge clk2in or posedge rst_in_o)
    if (rst_in_o)
      clk2_dly_cnt <= 6'b0;
    else
      if (clk2_dly_cnt < clk2_dt && clkout_en ==1)
        clk2_dly_cnt <= clk2_dly_cnt + 1;

  always  @(negedge clk3in or posedge rst_in_o)
    if (rst_in_o)
      clk3_dly_cnt <= 6'b0;
    else
      if (clk3_dly_cnt < clk3_dt && clkout_en ==1)
        clk3_dly_cnt <= clk3_dly_cnt + 1;

  always  @(negedge clk4in or posedge rst_in_o)
    if (rst_in_o)
        clk4_dly_cnt <= 6'b0;
    else
       if (clk4_dly_cnt < clk4_dt && clkout_en ==1)
          clk4_dly_cnt <= clk4_dly_cnt + 1;

  always  @(negedge clk5in or posedge rst_in_o)
    if (rst_in_o)
        clk5_dly_cnt <= 6'b0;
    else if (clkout_en == 1 ) begin
       if (clk5_dly_cnt < clk5_dt)
          clk5_dly_cnt <= clk5_dly_cnt + 1;
    end

  always  @(negedge clk6in or posedge rst_in_o)
    if (rst_in_o)
        clk6_dly_cnt <= 6'b0;
    else if (clkout_en == 1 ) begin
       if (clk6_dly_cnt < clk6_dt)
          clk6_dly_cnt <= clk6_dly_cnt + 1;
    end

  always  @(negedge clkfboutin or posedge rst_in_o)
    if (rst_in_o)
        clkfbout_dly_cnt <= 6'b0;
    else if (clkout_en == 1 ) begin
       if (clkfbout_dly_cnt < clkfbout_dt)
          clkfbout_dly_cnt <= clkfbout_dly_cnt + 1;
    end

  always @(posedge clkfboutin or negedge clkfboutin or posedge rst_in_o)
    if (rst_in_o || ~clkfbps_en) begin
      clkfbout_cnt <= 8'b0;
      clkfbout_out = 0;
    end
    else if (clkfbout_nc) clkfbout_out = ~clkfbout_out;
    else if (~clkfbout_frac_en) begin
      if (clkfbout_cnt < clkfbout_cnt_max)
        clkfbout_cnt <= clkfbout_cnt + 1;
      else
        clkfbout_cnt <= 8'b0;
      if (clkfbout_cnt < clkfbout_cnt_ht)
        clkfbout_out = 1;
      else
        clkfbout_out = 0;
      end
    else if (clkfbout_frac_en && clkfboutin) begin
      clkfbout_out = 1;
      clkfbout_frac_rm_rl = 0.0;
      clkfbout_frac_rm = 0;
      for (ib=1; ib < 8; ib=ib+1) begin
        clkfbout_frac_rm_rl = clkfbout_frac_rm_rl + clkfbout_frac_ht_rl - clkfbout_frac_ht - clkfbout_frac_rm;
        clkfbout_frac_rm = $rtoi(clkfbout_frac_rm_rl);
        #(clkfbout_frac_ht + clkfbout_frac_rm) clkfbout_out = 0;
        clkfbout_frac_rm_rl = clkfbout_frac_rm_rl + clkfbout_frac_lt_rl - clkfbout_frac_lt - clkfbout_frac_rm;
        clkfbout_frac_rm = $rtoi(clkfbout_frac_rm_rl);
        #(clkfbout_frac_lt + clkfbout_frac_rm) clkfbout_out = 1;
      end
      #(clkfbout_frac_ht) clkfbout_out = 0;
      #(clkfbout_frac_lt - period_vco1);
    end

  always @(posedge clk0in or negedge clk0in or posedge rst_in_o)
    if (rst_in_o || ~clk0ps_en) begin
      clk0_cnt <= 8'b0;
      clk0_out = 0;
    end
    else if (clk0_nc) clk0_out = ~clk0_out;
    else if (~clk0_frac_en) begin
      if (clk0_cnt < clk0_cnt_max)
        clk0_cnt <= clk0_cnt + 1;
      else
        clk0_cnt <= 8'b0; 
      if (clk0_cnt < clk0_cnt_ht)
        clk0_out = 1;
      else
        clk0_out = 0;
    end
    else if (clk0_frac_en && clk0in) begin
      clk0_out = 1;
      clk0_frac_rm_rl = 0.0;
      clk0_frac_rm = 0;
      for (ik0=1; ik0 < 8; ik0=ik0+1) begin
        clk0_frac_rm_rl = clk0_frac_rm_rl + clk0_frac_ht_rl - clk0_frac_ht - clk0_frac_rm;
        clk0_frac_rm = $rtoi(clk0_frac_rm_rl);
        #(clk0_frac_ht + clk0_frac_rm) clk0_out = 0;
        clk0_frac_rm_rl = clk0_frac_rm_rl + clk0_frac_lt_rl - clk0_frac_lt - clk0_frac_rm;
        clk0_frac_rm = $rtoi(clk0_frac_rm_rl);
        #(clk0_frac_lt + clk0_frac_rm) clk0_out = 1;
      end
      #(clk0_frac_ht) clk0_out = 0;
      #(clk0_frac_lt - period_vco1);
    end

  always @(posedge clk1in or negedge clk1in or posedge rst_in_o)
    if (rst_in_o || ~clk1ps_en) begin
      clk1_cnt <= 8'b0;
      clk1_out = 0;
    end
    else if (clk1_nc) clk1_out = ~clk1_out;
    else begin
      if (clk1_cnt < clk1_cnt_max)
        clk1_cnt <= clk1_cnt + 1;
      else
        clk1_cnt <= 8'b0; 
      if (clk1_cnt < clk1_cnt_ht)
        clk1_out = 1;
      else
        clk1_out = 0;
    end

  always @(posedge clk2in or negedge clk2in or posedge rst_in_o)
    if (rst_in_o || ~clk2ps_en) begin
      clk2_cnt <= 8'b0;
      clk2_out = 0;
    end
    else if (clk2_nc) clk2_out = ~clk2_out;
    else begin
      if (clk2_cnt < clk2_cnt_max)
        clk2_cnt <= clk2_cnt + 1;
      else
        clk2_cnt <= 8'b0; 
      if (clk2_cnt < clk2_cnt_ht)
        clk2_out = 1;
      else
        clk2_out = 0;
    end

  always @(posedge clk3in or negedge clk3in or posedge rst_in_o)
    if (rst_in_o || ~clk3ps_en) begin
      clk3_cnt <= 8'b0;
      clk3_out = 0;
    end
    else if (clk3_nc) clk3_out = ~clk3_out;
    else begin
      if (clk3_cnt < clk3_cnt_max)
        clk3_cnt <= clk3_cnt + 1;
      else
        clk3_cnt <= 8'b0; 
      if (clk3_cnt < clk3_cnt_ht)
        clk3_out = 1;
      else
        clk3_out = 0;
    end

  always @(posedge clk4in or negedge clk4in or posedge rst_in_o)
    if (rst_in_o || ~clk4ps_en) begin
      clk4_cnt <= 8'b0;
      clk4_out = 0;
    end
    else if (clk4_nc) clk4_out = ~clk4_out;
    else begin
      if (clk4_cnt < clk4_cnt_max)
        clk4_cnt <= clk4_cnt + 1;
      else
        clk4_cnt <= 8'b0; 
      if (clk4_cnt < clk4_cnt_ht)
        clk4_out = 1;
      else
        clk4_out = 0;
    end

  always @(posedge clk5in or negedge clk5in or posedge rst_in_o)
    if (rst_in_o || ~clk5ps_en) begin
      clk5_cnt <= 8'b0;
      clk5_out = 0;
    end
    else if (clk5_nc) clk5_out = ~clk5_out;
    else begin
      if (clk5_cnt < clk5_cnt_max)
        clk5_cnt <= clk5_cnt + 1;
      else
        clk5_cnt <= 8'b0; 
      if (clk5_cnt < clk5_cnt_ht)
        clk5_out = 1;
      else
        clk5_out = 0;
    end

  always @(posedge clk6in or negedge clk6in or posedge rst_in_o)
    if (rst_in_o || ~clk6ps_en) begin
      clk6_cnt <= 8'b0;
      clk6_out = 0;
    end
    else if (clk6_nc) clk6_out = ~clk6_out;
    else begin
      if (clk6_cnt < clk6_cnt_max)
        clk6_cnt <= clk6_cnt + 1;
      else
        clk6_cnt <= 8'b0; 
      if (clk6_cnt < clk6_cnt_ht)
        clk6_out = 1;
      else
        clk6_out = 0;
    end


   always @(clk0_out or clkfbout_tst or fb_delay_found)
     if (fb_delay_found == 1'b1) begin
          CLKOUT0_out  =  clk0_out;
          CLKOUT0B_out = ~clk0_out;
     end else begin
          CLKOUT0_out  =  clkfbout_tst;
          CLKOUT0B_out = ~clkfbout_tst;
     end

   always @(clk1_out or clkfbout_tst or fb_delay_found)
     if (fb_delay_found == 1'b1) begin
          CLKOUT1_out  =  clk1_out;
          CLKOUT1B_out = ~clk1_out;
     end else begin
          CLKOUT1_out  =  clkfbout_tst;
          CLKOUT1B_out = ~clkfbout_tst;
     end

   always @(clk2_out or clkfbout_tst or fb_delay_found)
     if (fb_delay_found == 1'b1) begin
          CLKOUT2_out  =  clk2_out;
          CLKOUT2B_out = ~clk2_out;
     end else begin
          CLKOUT2_out  =  clkfbout_tst;
          CLKOUT2B_out = ~clkfbout_tst;
     end

   always @(clk3_out or clkfbout_tst or fb_delay_found)
     if (fb_delay_found == 1'b1) begin
          CLKOUT3_out  =  clk3_out;
          CLKOUT3B_out = ~clk3_out;
     end else begin
          CLKOUT3_out  =  clkfbout_tst;
          CLKOUT3B_out = ~clkfbout_tst;
     end

   always @(clk4_out or clkfbout_tst or fb_delay_found)
     if (fb_delay_found == 1'b1) begin
          CLKOUT4_out  =  clk4_out;
     end else begin
          CLKOUT4_out  =  clkfbout_tst;
     end

   always @(clk5_out or clkfbout_tst or fb_delay_found)
     if (fb_delay_found == 1'b1) begin
          CLKOUT5_out  =  clk5_out;
     end else begin
          CLKOUT5_out  =  clkfbout_tst;
     end

   always @(clk6_out or clkfbout_tst or fb_delay_found)
     if (fb_delay_found == 1'b1) begin
          CLKOUT6_out  =  clk6_out;
     end else begin
          CLKOUT6_out  =  clkfbout_tst;
     end

   always @(clkfbout_out or clkfbout_tst or fb_delay_found)
     if (fb_delay_found == 1'b1)
        begin
          CLKFBOUT_out =  clkfbout_out;
          CLKFBOUTB_out =  ~clkfbout_out;
        end
     else
       begin
          CLKFBOUT_out = clkfbout_tst;
          CLKFBOUTB_out = ~clkfbout_tst;
       end

  //
  // determine feedback delay
  //


  always @(posedge clkpll_r )
    if (fb_delay_found) clkfbout_tst =  1'b0;
    else clkfbout_tst =  ~clkfbout_tst;

  always @( posedge clkfbout_tst )
      delay_edge = $time;

  assign clkfbin_sel = ((COMPENSATION_BIN == COMPENSATION_INTERNAL) ||
                        ((COMPENSATION_BIN == COMPENSATION_AUTO) && (CLKFBIN === 1'bz)));

  assign CLKFBIN_int = clkfbin_sel && CLKFBOUT_out || ~clkfbin_sel && CLKFBIN_in;

  always @(posedge CLKFBIN_int )
    if (clkfbin_sel == 1 ) begin
      fb_delay <= 0;
      fb_delay_found_tmp <=  1'b1;
    end else if (fb_delay_found_tmp == 1'b0 ) begin
      if ( delay_edge != 0) begin
        fb_delay <= ($time - delay_edge);
        fb_delay_found_tmp <=  1'b1;
      end else begin
        fb_delay <= 0;
        fb_delay_found_tmp <=  1'b0;
      end
    end

  always @(negedge clkfbout_tst or negedge fb_delay_found_tmp)
       fb_delay_found <= fb_delay_found_tmp;

  always @(fb_delay or fb_delay_found)
    if (rst_int==0 && fb_delay_found==1'b1 && (fb_delay/1000.0 > fb_delay_max)) begin
      $display("Warning: [Unisim %s-25] The feedback delay at time %t is %f ns. It is over the maximum value %f ns. Instance %m ", MODULE_NAME, $time, fb_delay / 1000.0, fb_delay_max);
    end

  //
  // generate unlock signal
  //

  always #(2*period_avg/3+250) clkin_osc = ~rst_int && ~clkin_osc;
  always #(2*period_avg*divclk_div/3+250) clkfbin_osc = ~rst_int && ~clkfbin_osc;

  always @(posedge clkpll_r or negedge clkpll_r) begin
      clkin_p <= 1;
      clkin_p <= #100 0;
  end

  always @(posedge CLKFBIN_int or negedge CLKFBIN_int) begin
      clkfbin_p <= 1;
      clkfbin_p <= #100 0;
  end

  always @(posedge clkin_osc or posedge rst_int or posedge clkin_p)
      if ((rst_int == 1) || (LOCKED == 1'b0)) begin
        clkinstopped_out1 <= 0;
        clkin_lost_cnt <= 0;
      end
      else if (clkin_p == 1) begin
        if (clkinstopped_out1 == 1) begin
          @(posedge clkpll_r) begin
          clkinstopped_out1 <= 0;
          clkin_lost_cnt <= 0;
          end
        end
        else begin
           clkinstopped_out1 <= 0;
           clkin_lost_cnt <= 0;
        end
      end
      else if (lock_period) begin
        if (clkin_lost_cnt < clkin_lost_val) begin
           clkin_lost_cnt <= clkin_lost_cnt + 1;
           clkinstopped_out1 <= 0;
        end
        else
           clkinstopped_out1 <= 1;
      end

  always @(posedge clkfbin_osc or posedge rst_int or posedge clkfbin_p)
      if (rst_int == 1 || clkfbin_p == 1) begin
        clkfbstopped_out1 <= 0;
        clkfbin_lost_cnt <= 0;
      end
      else if (clkout_en) begin
        if (clkfbin_lost_cnt < clkfbin_lost_val) begin
           clkfbin_lost_cnt <= clkfbin_lost_cnt + 1;
           clkfbstopped_out1 <= 0;
        end
        else
           clkfbstopped_out1 <= 1;
      end


  always @(clkin_jit or rst_int )
    if (rst_int)
       clkpll_jitter_unlock = 0;
    else
      if (pll_locked_tmp2 && clkfbstopped_out1 == 0 && clkinstopped_out1 == 0) begin
        if ((clkin_jit > REF_CLK_JITTER_MAX_tmp && clkin_jit < period_avg) ||
             (clkin_jit < -REF_CLK_JITTER_MAX_tmp && clkin_jit > -period_avg ))
          clkpll_jitter_unlock = 1;
        else
          clkpll_jitter_unlock = 0;
      end
      else
          clkpll_jitter_unlock = 0;

  assign pll_unlock1 = (clkinstopped_out_dly ==1 || clkfbstopped_out1==1 || clkpll_jitter_unlock == 1) ? 1 : 0;
  assign pll_unlock = (clkinstopped_out_dly ==1 || clkfbstopped_out1==1 || clkpll_jitter_unlock == 1 || unlock_recover == 1) ? 1 : 0;

  // tasks
task mc_to_attr;
    input [160:1] clkout_name;
    input [2:0] pm_f;
    input       wf_f;
    input [2:0] frac;
    input       frac_en;
    input       wf_r;
    input [1:0] mx;
    input       e;
    input       nc;
    input [5:0] dt;
    input [2:0] pm_r;
    input       en;
    input [5:0] ht;
    input [5:0] lt;
    output real div;
    output real phase;
    output real duty;

    integer odd_frac;
    reg odd;
    real frac_r;
    integer div_2;
    integer pm_f_c;
    real duty_step;
    real phase_step;

    reg [2:0] pm_f_calc;
    reg       wf_f_calc;
    reg [2:0] frac_calc;
    reg       frac_en_calc;
    reg       wf_r_calc;
    reg [1:0] mx_calc;
    reg       e_calc;
    reg       nc_calc;
    reg [5:0] dt_calc;
    reg [2:0] pm_r_calc;
    reg       en_calc;
    reg [5:0] ht_calc;
    reg [5:0] lt_calc;
    reg [34:0] calc;
    reg [34:0] actual;

begin

if (nc == 1'b1) begin
  div = 1.0;
  duty = 0.5;
end
else if (frac_en == 1'b1) begin
  duty =0.50;

  if (dt == 6'b0 && pm_r == 3'b0) pm_f_c = pm_f;
  else if (pm_f >= pm_r) pm_f_c = pm_f - pm_r;
  else pm_f_c = 8 + pm_f - pm_r;

  if (pm_f_c < 4) begin
    odd = 1'b0;
    odd_frac = frac;
  end
  else begin
    odd = 1'b1;
    odd_frac = frac + 8;
  end

  frac_r = frac * 0.125;

  if (odd_frac > 9) div_2 = lt;
  else div_2 = lt + 1;

  div = 2.0 * div_2 + 1.0 * odd + frac_r;

end
else begin

  if (ht == 6'b0 && lt == 6'b0) div = 128.0;
  else if (ht == 6'b0) div = 64.0 + lt * 1.0;
  else if (lt == 6'b0) div = ht * 1.0 + 64.0;
  else div = ht * 1.0 + lt * 1.0;

  duty_step = 0.5 / div;
    
  if (ht == 6'b0) duty = (2.0 * 64 + e) * duty_step;
  else duty = (2.0 * ht + e) * duty_step;

end

  phase_step = 360.0 / (div * 8.0);
  phase = phase_step * (dt*8.0 + pm_r*1.0);

  attr_to_mc(pm_f_calc, wf_f_calc, frac_calc, frac_en_calc, wf_r_calc, mx_calc, e_calc, nc_calc, dt_calc, pm_r_calc, en_calc, ht_calc, lt_calc, div, phase, duty);
  if (nc == 1'b1) begin
    calc = {pm_f, wf_f, frac, frac_en, wf_r, mx, e, nc_calc, dt, pm_r, en, ht, lt};
  end else begin
    calc = {pm_f_calc, wf_f_calc, frac_calc, frac_en_calc, wf_r_calc, mx_calc, e_calc, nc_calc, dt_calc, pm_r_calc, en_calc, ht_calc, lt_calc};
  end
  actual = {pm_f, wf_f, frac, frac_en, wf_r, mx, e, nc, dt, pm_r, en, ht, lt};
  if (actual != calc) begin
    $display("Error: [Unisim %s-36] Illegal counter DRP programming for %s at time %t. Instance %m ", MODULE_NAME, clkout_name, $time);
    if (pm_f_calc != pm_f) $display ("Error: [Unisim %s-37] pm_f calc ('b%b) different from pm_f programmed ('b%b) at time %t. Instance %m ", MODULE_NAME, pm_f_calc, pm_f, $time);
    if (wf_f_calc != wf_f) $display ("Error: [Unisim %s-37] wf_f calc ('b%b) different from wf_f programmed ('b%b) at time %t. Instance %m ", MODULE_NAME, wf_f_calc, wf_f, $time);
    if (frac_calc != frac) $display ("Error: [Unisim %s-37] frac calc ('b%b) different from frac programmed ('b%b) at time %t. Instance %m ", MODULE_NAME, frac_calc, frac, $time);
    if (frac_en_calc != frac_en) $display ("Error: [Unisim %s-37] frac_en calc ('b%b) different from frac_en programmed ('b%b) at time %t. Instance %m ", MODULE_NAME, frac_en_calc, frac_en, $time);
    if (wf_r_calc != wf_r) $display ("Error: [Unisim %s-37] wf_r calc ('b%b) different from wf_r programmed ('b%b) at time %t. Instance %m ", MODULE_NAME, wf_r_calc, wf_r, $time);
    if (mx_calc != mx) $display ("Error: [Unisim %s-37] mx calc ('b%b) different from mx programmed ('b%b) at time %t. Instance %m ", MODULE_NAME, mx_calc, mx, $time);
    if (e_calc != e) $display ("Error: [Unisim %s-37] e calc ('b%b) different from e programmed ('b%b) at time %t. Instance %m ", MODULE_NAME, e_calc, e, $time);
    if (nc_calc != nc) $display ("Error: [Unisim %s-37] nc calc ('b%b) different from nc programmed ('b%b) at time %t. Instance %m ", MODULE_NAME, nc_calc, nc, $time);
    if (dt_calc != dt) $display ("Error: [Unisim %s-37] dt calc ('b%b) different from dt programmed ('b%b) at time %t. Instance %m ", MODULE_NAME, dt_calc, dt, $time);
    if (pm_r_calc != pm_r) $display ("Error: [Unisim %s-37] pm_r calc ('b%b) different from pm_r programmed ('b%b) at time %t. Instance %m ", MODULE_NAME, pm_r_calc, pm_r, $time);
    if (en_calc != en) $display ("Error: [Unisim %s-37] en calc ('b%b) different from en programmed ('b%b) at time %t. Instance %m ", MODULE_NAME, en_calc, en, $time);
    if (ht_calc != ht) $display ("Error: [Unisim %s-37] ht calc ('b%b) different from ht programmed ('b%b) at time %t. Instance %m ", MODULE_NAME, ht_calc, ht, $time);
    if (lt_calc != lt) $display ("Error: [Unisim %s-37] lt calc ('b%b) different from lt programmed ('b%b) at time %t. Instance %m ", MODULE_NAME, lt_calc, lt, $time);
  end
end
endtask 

task upper_mix_drp;
    output reg [2:0] pm_f;
    output reg       wf_f;
    output reg cddc_en;
    output reg [1:0] mx;
    output reg       e;
    output reg       nc;
    output reg [5:0] dt;
    input [15:0] DI;
begin
    pm_f = DI[15:13];
    wf_f = DI[12];
    cddc_en = DI[10];
    mx = DI[9:8];
    e = DI[7];
    nc = DI[6];
    dt = DI[5:0];
end
endtask 

task upper_frac_drp;
    output reg       cddc_en;
    output reg [2:0] frac;
    output reg       frac_en;
    output reg       wf_r;
    output reg [1:0] mx;
    output reg       e;
    output reg       nc;
    output reg [5:0] dt;
    input [15:0] DI;
begin
    cddc_en = DI[15];
    frac = DI[14:12];
    frac_en = DI[11];
    wf_r = DI[10];
    mx = DI[9:8];
    e = DI[7];
    nc = DI[6];
    dt = DI[5:0];
end
endtask 

task upper_drp;
    output reg        cddc_en;
    output reg [1:0] mx;
    output reg       e;
    output reg       nc;
    output reg [5:0] dt;
    input [15:0] DI;
begin
    cddc_en = DI[10];
    mx = DI[9:8];
    e = DI[7];
    nc = DI[6];
    dt = DI[5:0];
end
endtask 

task lower_drp;
    output reg [2:0] pm_r;
    output reg       en;
    output reg [5:0] ht;
    output reg [5:0] lt;
    input [15:0] DI;
begin
    pm_r = DI[15:13];
    en = DI[12];
    ht = DI[11:6];
    lt = DI[5:0];
end
endtask 

//ht_calc( frac, frac_en, e, ht, lt, div_f, clk_rsel, clk_fsel, clk_fht, clk_flt, clk_cnt_max, clk_cnt_ht, clk_div)
task ht_calc;
    input [2:0] frac;
    input       frac_en;
    input       e;
    input [5:0] ht;
    input [6:0] lt;
    input real  f_div;
    output [3:0] clk_rsel;
    output [3:0] clk_fsel;
    output [6:0] clk_fht;
    output [6:0] clk_flt;
    output integer clk_cnt_max;
    output integer clk_cnt_ht;
    output integer clk_div_fint;

    integer clk_div_fint_odd;
begin
    clk_div_fint = $rtoi(f_div);
    if (frac_en) begin
      clk_fht = clk_div_fint / 2;
      clk_flt = clk_div_fint / 2;
      clk_div_fint_odd = clk_div_fint - clk_fht - clk_flt;
      if (clk_div_fint_odd > 0) begin
        clk_rsel = (8 + frac) / 2;
        clk_fsel =  8 + frac - clk_rsel;
      end
      else begin
        clk_rsel = frac / 2;
        clk_fsel = frac - clk_rsel;
      end
    end
    else begin
      if (ht == 6'b0) clk_fht = 64; else clk_fht = ht;
      if (lt == 7'b0) clk_flt = 64; else clk_flt = lt;
      clk_cnt_max = 2 * (clk_fht + clk_flt) - 1;
      clk_cnt_ht = 2 * clk_fht + e;
    end

end
endtask 

task attr_to_mc;
    output reg [2:0] pm_f;
    output reg       wf_f;
    output reg [2:0] frac;
    output reg       frac_en;
    output reg       wf_r;
    output reg [1:0] mx;
    output reg       e;
    output reg       nc;
    output reg [5:0] dt;
    output reg [2:0] pm_r;
    output reg       en;
    output reg [5:0] ht;
    output reg [5:0] lt;
    input real div;
    input real phase;
    input real duty;

    integer div_int;
    real div_frac;
    real div_rnd;

    reg [37:0] vector;
begin

// determine frac_en
    div_int = $rtoi(div);
    div_frac = div - $itor(div_int);
    if (div_frac > 0.000) frac_en = 1'b1;
    else frac_en = 1'b0;

// rnd frac to nearest 0.125 - may become .000
    div_rnd = $itor($rtoi((div + 0.0625) * 8.0)) / 8.0;

// determine int and frac part
    div_int = $rtoi(div_rnd);
    div_frac = div_rnd - $itor(div_int);
 
    if (frac_en == 1'b1)
      vector = mmcm_frac_calc(div_int,phase*1000,duty*100000,div_frac*1000);
    else
      vector = mmcm_calc(div_int,phase*1000,duty*100000);

      if (frac_en == 1'b1) begin
        pm_f = vector[35:33];
        wf_f = vector[32];
        frac = vector[30:28];
        frac_en = vector[27];
        wf_r = vector[26];
      end
      else begin
        pm_f = 3'b0;
        wf_f = 1'b0;
        frac = 3'b0;
        frac_en = 1'b0;
        wf_r = 1'b0;
      end
      mx = vector[25:24];
      e = vector[23];
      en = 1'b1;
    if (div_int == 1) begin
      nc = 1'b1;
      ht = 6'b1;
      lt = 6'b1;
    end else begin
      nc = vector[22];
      ht = vector[11:6];
      lt = vector[5:0];
    end
      dt = vector[21:16];
      pm_r = vector[15:13];
end
endtask 

`define MMCME4_ADV_FRAC_PRECISION  10
`define MMCME4_ADV_FIXED_WIDTH     32 

// This function takes a fixed point number and rounds it to the nearest
//    fractional precision bit.
function [`MMCME4_ADV_FIXED_WIDTH:1] round_frac
   (
      // Input is (FIXED_WIDTH-FRAC_PRECISION).FRAC_PRECISION fixed point number
      input [`MMCME4_ADV_FIXED_WIDTH:1] decimal,  

      // This describes the precision of the fraction, for example a value
      //    of 1 would modify the fractional so that instead of being a .16
      //    fractional, it would be a .1 (rounded to the nearest 0.5 in turn)
      input [`MMCME4_ADV_FIXED_WIDTH:1] precision 
   );

   begin
   
      // If the fractional precision bit is high then round up
      if( decimal[(`MMCME4_ADV_FRAC_PRECISION-precision)] == 1'b1) begin
         round_frac = decimal + (1'b1 << (`MMCME4_ADV_FRAC_PRECISION-precision));
      end else begin
         round_frac = decimal;
      end
   end
endfunction

// This function calculates high_time, low_time, w_edge, and no_count
//    of a non-fractional counter based on the divide and duty cycle
//
// NOTE: high_time and low_time are returned as integers between 0 and 63 
//    inclusive.  64 should equal 6'b000000 (in other words it is okay to 
//    ignore the overflow)
function [13:0] mmcm_divider
   (
      input [7:0] divide,        // Max divide is 128
      input [31:0] duty_cycle    // Duty cycle is multiplied by 100,000
   );

   reg [`MMCME4_ADV_FIXED_WIDTH:1]    duty_cycle_fix;
   
   // High/Low time is initially calculated with a wider integer to prevent a
   // calculation error when it overflows to 64.
   reg [6:0]               high_time;
   reg [6:0]               low_time;
   reg                     w_edge;
   reg                     no_count;

   reg [`MMCME4_ADV_FIXED_WIDTH:1]    temp;

   begin
      // Duty Cycle must be between 0 and 1,000
      if(duty_cycle <=0 || duty_cycle >= 100000) begin
         $display("ERROR: duty_cycle: %d is invalid", duty_cycle);
         $finish;
      end

      // Convert to FIXED_WIDTH-FRAC_PRECISION.FRAC_PRECISION fixed point
      duty_cycle_fix = (duty_cycle << `MMCME4_ADV_FRAC_PRECISION) / 100_000;
      
      // If the divide is 1 nothing needs to be set except the no_count bit.
      //    Other values are dummies
      if(divide == 7'h01) begin
         high_time   = 7'h01;
         w_edge      = 1'b0;
         low_time    = 7'h01;
         no_count    = 1'b1;
      end else begin
         temp = round_frac(duty_cycle_fix*divide, 1);
         // comes from above round_frac
         high_time   = temp[`MMCME4_ADV_FRAC_PRECISION+7:`MMCME4_ADV_FRAC_PRECISION+1]; 
         // If the duty cycle * divide rounded is .5 or greater then this bit
         //    is set.
         w_edge      = temp[`MMCME4_ADV_FRAC_PRECISION]; // comes from round_frac
         
         // If the high time comes out to 0, it needs to be set to at least 1
         // and w_edge set to 0
         if(high_time == 7'h00) begin
            high_time   = 7'h01;
            w_edge      = 1'b0;
         end

         if(high_time == divide) begin
            high_time   = divide - 1;
            w_edge      = 1'b1;
         end
         
         // Calculate low_time based on the divide setting and set no_count to
         //    0 as it is only used when divide is 1.
         low_time    = divide - high_time; 
         no_count    = 1'b0;
      end

      // Set the return value.
      mmcm_divider = {w_edge,no_count,high_time[5:0],low_time[5:0]};
   end
endfunction

// This function calculates mx, delay_time, and phase_mux 
//  of a non-fractional counter based on the divide and phase
//
// NOTE: The only valid value for the MX bits is 2'b00 to ensure the coarse mux
//    is used.
function [10:0] mmcm_phase
   (
      // divide must be an integer (use fractional if not)
      //  assumed that divide already checked to be valid
      input [7:0] divide, // Max divide is 128

      // Phase is given in degrees (-360,000 to 360,000)
      input signed [31:0] phase
   );

   reg [`MMCME4_ADV_FIXED_WIDTH:1] phase_in_cycles;
   reg [`MMCME4_ADV_FIXED_WIDTH:1] phase_fixed;
   reg [1:0]            mx;
   reg [5:0]            delay_time;
   reg [2:0]            phase_mux;

   reg [`MMCME4_ADV_FIXED_WIDTH:1] temp;

   begin
      if ((phase < -360000) || (phase > 360000)) begin
         $display("ERROR: phase of (%d) is not between -360000 and 360000. Instance %m",phase);
         $finish;
      end

      // If phase is less than 0, convert it to a positive phase shift
      // Convert to (FIXED_WIDTH-FRAC_PRECISION).FRAC_PRECISION fixed point
      if(phase < 0) begin
         phase_fixed = ( (phase + 360000) << `MMCME4_ADV_FRAC_PRECISION ) / 1000;
      end else begin
         phase_fixed = ( phase << `MMCME4_ADV_FRAC_PRECISION ) / 1000;
      end

      // Put phase in terms of decimal number of vco clock cycles
      phase_in_cycles = ( phase_fixed * divide ) / 360;

   temp  =  round_frac(phase_in_cycles, 3);

   // set mx to 2'b00 that the phase mux from the VCO is enabled
   mx          =  2'b00; 
   phase_mux      =  temp[`MMCME4_ADV_FRAC_PRECISION:`MMCME4_ADV_FRAC_PRECISION-2];
   delay_time     =  temp[`MMCME4_ADV_FRAC_PRECISION+6:`MMCME4_ADV_FRAC_PRECISION+1];
      
      // Setup the return value
      mmcm_phase={mx, phase_mux, delay_time};
   end
endfunction

// This function takes in the divide, phase, and duty cycle
// setting to calculate the upper and lower counter registers.
function [37:0] mmcm_calc
   (
      input [7:0] divide, // Max divide is 128
      input signed [31:0] phase,
      input [31:0] duty_cycle // Multiplied by 100,000
   );
   
   reg [13:0] div_calc;
   reg [16:0] phase_calc;
   
   begin
      // w_edge[13], no_count[12], high_time[11:6], low_time[5:0]
      div_calc = mmcm_divider(divide, duty_cycle);
      // mx[10:9], pm[8:6], dt[5:0]
      phase_calc = mmcm_phase(divide, phase);

      // Return value is the upper and lower address of counter
      //    Upper address is:
      //       RESERVED    [31:26]
      //       MX          [25:24]
      //       EDGE        [23]
      //       NOCOUNT     [22]
      //       DELAY_TIME  [21:16]
      //    Lower Address is:
      //       PHASE_MUX   [15:13]
      //       RESERVED    [12]
      //       HIGH_TIME   [11:6]
      //       LOW_TIME    [5:0]
      
      mmcm_calc =
         {
            // Upper Address
            6'h00, phase_calc[10:9], div_calc[13:12], phase_calc[5:0], 
            // Lower Address
            phase_calc[8:6], 1'b0, div_calc[11:0]
         };
   end
endfunction

// This function takes in the divide, phase, and duty cycle
// setting to calculate the upper and lower counter registers.
// for fractional multiply/divide functions.
//
// 
function [37:0] mmcm_frac_calc
   (
      input [7:0] divide, // Max divide is 128
      input signed [31:0] phase,
      input [31:0] duty_cycle, // Multiplied by 100,000
      input [9:0] frac // Multiplied by 1000
   );
   
  //Required for fractional divide calculations
        reg  [7:0]      lt_frac;
        reg  [7:0]      ht_frac;
      
        reg  /*[7:0]*/      wf_fall_frac;
        reg  /*[7:0]*/      wf_rise_frac;

        reg [31:0] a;
        reg  [7:0]      pm_rise_frac_filtered ;
        reg  [7:0]      pm_fall_frac_filtered ;  
        reg [7:0]      clkout0_divide_int;
        reg [2:0]      clkout0_divide_frac;
        reg  [7:0]      even_part_high;
        reg  [7:0]      even_part_low;

        reg  [7:0]      odd;
        reg  [7:0]      odd_and_frac;

        reg  [7:0]      pm_fall;
        reg  [7:0]      pm_rise;
        reg  [7:0]      dt;
        reg  [7:0]      dt_int; 
        reg [63:0]    dt_calc;

        reg  [7:0]      pm_rise_frac; 
        reg  [7:0]      pm_fall_frac;
   
        reg [31:0] a_per_in_octets;
        reg [31:0] a_phase_in_cycles;

        reg [31:0] phase_fixed; // changed to 31:0 from 32:1 jt 5/2/11
        reg [31: 0] phase_pos;
        reg [31: 0] phase_vco;
        reg [31:0] temp;// changed to 31:0 from 32:1 jt 5/2/11
        reg [13:0] div_calc;
        reg [16:0] phase_calc;

   begin
   //convert phase to fixed
   if ((phase < -360000) || (phase > 360000)) begin
      $display("ERROR: phase of (%d) is not between -360000 and 360000. Instance %m",phase);
//      $display("ERROR: phase of $phase is not between -360000 and 360000");
      $finish;
   end


      // Return value is
      //    Transfer data
      //       RESERVED     [37:36]
      //       FRAC_TIME    [35:33]
      //       FRAC_WF_FALL [32]
      //    Upper address is:
      //       RESERVED     [31:26]
      //       MX           [25:24]
      //       EDGE         [23]
      //       NOCOUNT      [22]
      //       DELAY_TIME   [21:16]
      //    Lower Address is:
      //       PHASE_MUX    [15:13]
      //       RESERVED     [12]
      //       HIGH_TIME    [11:6]
      //       LOW_TIME     [5:0]
      
      

  clkout0_divide_frac = frac / 125;
  clkout0_divide_int = divide;

  even_part_high = clkout0_divide_int >> 1;//$rtoi(clkout0_divide_int / 2);
  even_part_low = even_part_high;
                  
  odd = clkout0_divide_int - even_part_high - even_part_low;
  odd_and_frac = (8*odd) + clkout0_divide_frac;

  lt_frac = even_part_high - (odd_and_frac <= 9);//IF(odd_and_frac>9,even_part_high, even_part_high - 1)
  ht_frac = even_part_low  - (odd_and_frac <= 8);//IF(odd_and_frac>8,even_part_low, even_part_low- 1)

  pm_fall =  {odd[6:0],2'b00} + {6'h00, clkout0_divide_frac[2:1]}; // using >> instead of clkout0_divide_frac / 2 
  pm_rise = 0; //0
    
  wf_fall_frac = ((odd_and_frac >=2) && (odd_and_frac <=9)) || ((clkout0_divide_frac == 1) && (clkout0_divide_int == 2));//CRS610807
  wf_rise_frac = (odd_and_frac >=1) && (odd_and_frac <=8);//IF(odd_and_frac>=1,IF(odd_and_frac <= 8,1,0),0)



  //Calculate phase in fractional cycles
  a_per_in_octets    = (8 * divide) + (frac / 125) ;
  a_phase_in_cycles  = (phase+10) * a_per_in_octets / 360000 ;//Adding 1 due to rounding errors
  pm_rise_frac    = (a_phase_in_cycles[7:0] ==8'h00)?8'h00:a_phase_in_cycles[7:0] - {a_phase_in_cycles[7:3],3'b000};

  dt_calc   = ((phase+10) * a_per_in_octets / 8 )/360000 ;//TRUNC(phase* divide / 360); //or_simply (a_per_in_octets / 8)
  dt   = dt_calc[7:0];

  pm_rise_frac_filtered = (pm_rise_frac >=8) ? (pm_rise_frac ) - 8: pm_rise_frac ;        //((phase_fixed * (divide + frac / 1000)) / 360) - {pm_rise_frac[7:3],3'b000};//$rtoi(clkout0_phase * clkout0_divide / 45);//a;

  dt_int      = dt + (& pm_rise_frac[7:4]); //IF(pm_rise_overwriting>7,dt+1,dt)
  pm_fall_frac    = pm_fall + pm_rise_frac;
  pm_fall_frac_filtered  = pm_fall + pm_rise_frac - {pm_fall_frac[7:3], 3'b000};

  div_calc  = mmcm_divider(divide, duty_cycle); //Not used since edge and no count are 0 when fractional
  phase_calc  = mmcm_phase(divide, phase);// returns{mx[1:0], phase_mux[2:0], delay_time[5:0]}
    
      mmcm_frac_calc[37:0] =
         {    2'b00, pm_fall_frac_filtered[2:0], wf_fall_frac,
      1'b0, clkout0_divide_frac[2:0], 1'b1, wf_rise_frac, phase_calc[10:9], 2'b00, dt[5:0], 
      pm_rise_frac_filtered[2], pm_rise_frac_filtered[1], pm_rise_frac_filtered[0], 1'b0, ht_frac[5:0], lt_frac[5:0]
    } ;

   end
endfunction

  function  clkout_duty_chk;
  input  CLKOUT_DIVIDE;
  input  CLKOUT_DUTY_CYCLE;
  input reg [160:0] CLKOUT_DUTY_CYCLE_N;
  integer CLKOUT_DIVIDE, step_tmp;
  real CLKOUT_DUTY_CYCLE;
  real CLK_DUTY_CYCLE_MIN, CLK_DUTY_CYCLE_MAX, CLK_DUTY_CYCLE_CHK, CLK_DUTY_CYCLE_STEP;
  real CLK_DUTY_CYCLE_MIN_rnd;
  reg clk_duty_tmp_int;
  begin
    if (CLKOUT_DIVIDE > O_MAX_HT_LT) begin
      CLK_DUTY_CYCLE_MIN = 1.0 * (CLKOUT_DIVIDE - O_MAX_HT_LT)/CLKOUT_DIVIDE;
      CLK_DUTY_CYCLE_MAX = (O_MAX_HT_LT      )/CLKOUT_DIVIDE;
      CLK_DUTY_CYCLE_CHK = (O_MAX_HT_LT + 0.5)/CLKOUT_DIVIDE;
      CLK_DUTY_CYCLE_MIN_rnd = CLK_DUTY_CYCLE_MIN;
    end
    else begin
      if (CLKOUT_DIVIDE == 1) begin
        CLK_DUTY_CYCLE_MIN = 0.0;
        CLK_DUTY_CYCLE_MIN_rnd = 0.0;
      end
      else begin
        step_tmp = 1000 / CLKOUT_DIVIDE;
        CLK_DUTY_CYCLE_MIN_rnd = step_tmp / 1000.0;
        CLK_DUTY_CYCLE_MIN = 1.0 /CLKOUT_DIVIDE;
      end
      CLK_DUTY_CYCLE_CHK = 1.0;
      CLK_DUTY_CYCLE_MAX = 1.0;
    end

    if (CLKOUT_DUTY_CYCLE > CLK_DUTY_CYCLE_CHK || CLKOUT_DUTY_CYCLE < CLK_DUTY_CYCLE_MIN_rnd) begin
      $display("Warning: [Unisim %s-30] %s is set to %f and is not in the allowed range %f to %f. Instance %m ", MODULE_NAME, CLKOUT_DUTY_CYCLE_N, CLKOUT_DUTY_CYCLE, CLK_DUTY_CYCLE_MIN, CLK_DUTY_CYCLE_MAX );
    end

    clk_duty_tmp_int = 0;
    CLK_DUTY_CYCLE_STEP = 0.5 / CLKOUT_DIVIDE;
    for (j = 0; j < (2 * CLKOUT_DIVIDE - CLK_DUTY_CYCLE_MIN/CLK_DUTY_CYCLE_STEP); j = j + 1)
        if (((CLK_DUTY_CYCLE_MIN + CLK_DUTY_CYCLE_STEP * j) - CLKOUT_DUTY_CYCLE) > -0.001 &&
             ((CLK_DUTY_CYCLE_MIN + CLK_DUTY_CYCLE_STEP * j) - CLKOUT_DUTY_CYCLE) < 0.001)
            clk_duty_tmp_int = 1;

    if ( clk_duty_tmp_int != 1) begin
      $display("Warning: [Unisim %s-31] %s is set to %f and is not an allowed value. Allowed values are:",  MODULE_NAME, CLKOUT_DUTY_CYCLE_N, CLKOUT_DUTY_CYCLE);
      for (j = 0; j < (2 * CLKOUT_DIVIDE - CLK_DUTY_CYCLE_MIN/CLK_DUTY_CYCLE_STEP); j = j + 1)
       $display("%f", CLK_DUTY_CYCLE_MIN + CLK_DUTY_CYCLE_STEP * j);
      $display(" Instance %m ");
    end

    clkout_duty_chk = 1'b1;
  end
  endfunction

  function  para_int_range_chk;
  input  para_in;
  input reg [160:0] para_name;
  input  range_low;
  input  range_high;
  integer para_in;
  integer range_low;
  integer  range_high;
  begin
    if ( para_in < range_low || para_in > range_high) begin
      $display("Error: [Unisim %s-32] The Attribute %s is set to %d.  Legal values for this attribute are %d to %d. Instance %m ", MODULE_NAME, para_name, para_in, range_low, range_high);
      $finish;
    end
    para_int_range_chk = 1'b1;
  end
  endfunction

  function  para_real_range_chk;
  input  para_in;
  input reg [160:0] para_name;
  input  range_low;
  input  range_high;
  real para_in;
  real range_low;
  real range_high;
  begin
    if ( para_in < range_low || para_in > range_high) begin
      $display("Error : [Unisim %s-33] The Attribute %s is set to %f.  Legal values for this attribute are %f to %f. Instance %m ", MODULE_NAME, para_name, para_in, range_low, range_high);
      $finish;
    end
    para_real_range_chk = 1'b0;
  end
  endfunction

task check_m_settings;
  input real clkfbout_f_div;
  input [3:0] pll_cp;
  input [3:0] pll_res;
  input [4:0] drp_lock_ref_dly;
  input [4:0] drp_lock_fb_dly;
  input [9:0] drp_lock_cnt;
  input [9:0] drp_unlock_cnt;
  input [9:0] drp_lock_sat_high;

  integer clkfbout_div;
  reg [3:0] pll_cp_low, pll_cp_high, pll_cp_optimized;
  reg [3:0] pll_res_low, pll_res_high, pll_res_optimized;
  reg [4:0] drp_lock_ref_dly_calc;
  reg [4:0] drp_lock_fb_dly_calc;
  reg [9:0] drp_lock_cnt_calc;
  reg [9:0] drp_unlock_cnt_calc;
  reg [9:0] drp_lock_sat_high_calc;
  reg [47:0] actual;
  reg [47:0] calc_low, calc_high, calc_optimized;

begin

  actual = {pll_cp,pll_res,drp_lock_ref_dly,drp_lock_fb_dly,drp_lock_cnt,drp_lock_sat_high,drp_unlock_cnt};
  clkfbout_div = $rtoi(clkfbout_f_div);
  GetMultVal(clkfbout_div,nBandwidth_LOW,pll_cp_low,pll_res_low);
  GetMultVal(clkfbout_div,nBandwidth_HIGH,pll_cp_high,pll_res_high);
  GetMultVal(clkfbout_div,nBandwidth_OPTIMIZED,pll_cp_optimized,pll_res_optimized);
  GetLockDetSettings(clkfbout_div,drp_lock_ref_dly_calc,drp_lock_fb_dly_calc,drp_lock_cnt_calc,drp_lock_sat_high_calc,drp_unlock_cnt_calc);
  calc_low = {pll_cp_low,pll_res_low,drp_lock_ref_dly_calc,drp_lock_fb_dly_calc,drp_lock_cnt_calc,drp_lock_sat_high_calc,drp_unlock_cnt_calc};
  calc_high = {pll_cp_high,pll_res_high,drp_lock_ref_dly_calc,drp_lock_fb_dly_calc,drp_lock_cnt_calc,drp_lock_sat_high_calc,drp_unlock_cnt_calc};
  calc_optimized = {pll_cp_optimized,pll_res_optimized,drp_lock_ref_dly_calc,drp_lock_fb_dly_calc,drp_lock_cnt_calc,drp_lock_sat_high_calc,drp_unlock_cnt_calc};

  if (actual != calc_low && actual != calc_high && actual != calc_optimized)
    $display("Error: [Unisim %s-35] Illegal cp, res, and/or lock DRP programming at time %t. Programmed vales do not match Bandwidth setting. Instance %m ", MODULE_NAME, $time);

end
endtask

task GetLockDetSettings (input integer fClkFbOutMultF, output [4:0] lock_ref_dly, output [4:0] lock_fb_dly, output [9:0] lock_cnt, output [9:0] lock_sat_high, output [9:0] unlock_cnt);
 begin
   lock_sat_high = 10'd1001;
   unlock_cnt = 10'd1;
   case (fClkFbOutMultF)
      1,2: begin
           lock_ref_dly = 5'd6;
           lock_fb_dly = 5'd6;
           lock_cnt = 10'd1000;
         end
      3: begin
           lock_ref_dly = 5'd8;
           lock_fb_dly = 5'd8;
           lock_cnt = 10'd1000;
         end
      4: begin
           lock_ref_dly = 5'd11;
           lock_fb_dly = 5'd11;
           lock_cnt = 10'd1000;
         end
      5: begin
           lock_ref_dly = 5'd14;
           lock_fb_dly = 5'd14;
           lock_cnt = 10'd1000;
         end
      6: begin
           lock_ref_dly = 5'd17;
           lock_fb_dly = 5'd17;
           lock_cnt = 10'd1000;
         end
      7: begin
           lock_ref_dly = 5'd19;
           lock_fb_dly = 5'd19;
           lock_cnt = 10'd1000;
         end
      8: begin
           lock_ref_dly = 5'd22;
           lock_fb_dly = 5'd22;
           lock_cnt = 10'd1000;
         end
      9: begin
           lock_ref_dly = 5'd25;
           lock_fb_dly = 5'd25;
           lock_cnt = 10'd1000;
         end
      10: begin
           lock_ref_dly = 5'd28;
           lock_fb_dly = 5'd28;
           lock_cnt = 10'd1000;
         end
      11: begin
           lock_ref_dly = 5'd31;
           lock_fb_dly = 5'd31;
           lock_cnt = 10'd900;
         end
      12: begin
           lock_ref_dly = 5'd31;
           lock_fb_dly = 5'd31;
           lock_cnt = 10'd825;
         end
      13: begin
           lock_ref_dly = 5'd31;
           lock_fb_dly = 5'd31;
           lock_cnt = 10'd750;
         end
      14: begin
           lock_ref_dly = 5'd31;
           lock_fb_dly = 5'd31;
           lock_cnt = 10'd700;
         end
      15: begin
           lock_ref_dly = 5'd31;
           lock_fb_dly = 5'd31;
           lock_cnt = 10'd650;
         end
      16: begin
           lock_ref_dly = 5'd31;
           lock_fb_dly = 5'd31;
           lock_cnt = 10'd625;
         end
      17: begin
           lock_ref_dly = 5'd31;
           lock_fb_dly = 5'd31;
           lock_cnt = 10'd575;
         end
      18: begin
           lock_ref_dly = 5'd31;
           lock_fb_dly = 5'd31;
           lock_cnt = 10'd550;
         end
      19: begin
           lock_ref_dly = 5'd31;
           lock_fb_dly = 5'd31;
           lock_cnt = 10'd525;
         end
      20: begin
           lock_ref_dly = 5'd31;
           lock_fb_dly = 5'd31;
           lock_cnt = 10'd500;
         end
      21: begin
           lock_ref_dly = 5'd31;
           lock_fb_dly = 5'd31;
           lock_cnt = 10'd475;
         end
      22: begin
           lock_ref_dly = 5'd31;
           lock_fb_dly = 5'd31;
           lock_cnt = 10'd450;
         end
      23: begin
           lock_ref_dly = 5'd31;
           lock_fb_dly = 5'd31;
           lock_cnt = 10'd425;
         end
      24,25: begin
           lock_ref_dly = 5'd31;
           lock_fb_dly = 5'd31;
           lock_cnt = 10'd400;
         end
      26: begin
           lock_ref_dly = 5'd31;
           lock_fb_dly = 5'd31;
           lock_cnt = 10'd375;
         end
      27,28: begin
           lock_ref_dly = 5'd31;
           lock_fb_dly = 5'd31;
           lock_cnt = 10'd350;
         end
      29,30: begin
           lock_ref_dly = 5'd31;
           lock_fb_dly = 5'd31;
           lock_cnt = 10'd325;
         end
      31,32,33: begin
           lock_ref_dly = 5'd31;
           lock_fb_dly = 5'd31;
           lock_cnt = 10'd300;
         end
      34,35,36: begin
           lock_ref_dly = 5'd31;
           lock_fb_dly = 5'd31;
           lock_cnt = 10'd275;
         end
      default: begin
           lock_ref_dly = 5'd31;
           lock_fb_dly = 5'd31;
           lock_cnt = 10'd250;
         end
   endcase
 end
endtask

task GetMultVal (input integer fClkFbOutMultF, input integer nBandwidth, output [3:0] cp, output [3:0] res);
 begin
   if ((nBandwidth == nBandwidth_HIGH) || (nBandwidth == nBandwidth_OPTIMIZED))
      case (fClkFbOutMultF)
         2: begin
              cp = 4'd7; res = 4'd15;
            end
         3: begin
              cp = 4'd14; res = 4'd15;
            end
         4: begin
              cp = 4'd15; res = 4'd15;
            end
         5: begin
              cp = 4'd15; res = 4'd11;
            end
         6: begin
              cp = 4'd15; res = 4'd13;
            end
         7: begin
              cp = 4'd15; res = 4'd3;
            end
         8: begin
              cp = 4'd14; res = 4'd5;
            end
         9,10: begin
              cp = 4'd15; res = 4'd9;
            end
         11: begin
              cp = 4'd14; res = 4'd14;
            end
         12: begin
              cp = 4'd15; res = 4'd14;
            end
         13,14,15: begin
              cp = 4'd15; res = 4'd1;
            end
         16,17: begin
              cp = 4'd14; res = 4'd6;
            end
         18: begin
              cp = 4'd15; res = 4'd6;
            end
         19,20: begin
              cp = 4'd14; res = 4'd10;
            end
         21,22,23,24,25: begin
              cp = 4'd15; res = 4'd10;
            end
         26,27,28: begin
              cp = 4'd13; res = 4'd12;
            end
         29,30,31: begin
              cp = 4'd14; res = 4'd12;
            end
         32,33,34,35,36,37: begin
              cp = 4'd15; res = 4'd12;
            end
         38,39,40,41: begin
              cp = 4'd14; res = 4'd2;
            end
         42,43,44,45,46,47,48,49,50,51,52,53,54,55,56,57,58,59,60,61,62: begin
              cp = 4'd15; res = 4'd2;
            end
         63,64,65,66,67,68,69,70: begin
              cp = 4'd12; res = 4'd4;
            end
         71,72,73,74,75,76,77: begin
              cp = 4'd13; res = 4'd4;
            end
         78,79,80,81,82,83,84,85: begin
              cp = 4'd14; res = 4'd4;
            end
         86,87,88,89,90,91,92,93,94,95,96,97,98,99,100,101,102,103,104,105,106,107,108,109,110,111,112,113,114,115,116,117,118,119: begin
              cp = 4'd15; res = 4'd4;
            end
         120,121,122,123,124,125,126,127,128: begin
              cp = 4'd13; res = 4'd8;
            end
      endcase
   else if (nBandwidth == nBandwidth_LOW) begin
      case (fClkFbOutMultF)
         2: begin
              cp = 4'd3; res = 4'd15;
            end
         3: begin
              cp = 4'd3; res = 4'd13;
            end
         4: begin
              cp = 4'd3; res = 4'd5;
            end
         5: begin
              cp = 4'd3; res = 4'd9;
            end
         6,7: begin
              cp = 4'd3; res = 4'd14;
            end
         8: begin
              cp = 4'd3; res = 4'd1;
            end
         9,10,11: begin
              cp = 4'd3; res = 4'd6;
            end
         12,13,14: begin
              cp = 4'd3; res = 4'd10;
            end
         15: begin
              cp = 4'd4; res = 4'd6;
            end
         16: begin
              cp = 4'd3; res = 4'd12;
            end
         17: begin
              cp = 4'd14; res = 4'd6;
            end
         18: begin
              cp = 4'd15; res = 4'd6;
            end
         19,20: begin
              cp = 4'd14; res = 4'd10;
            end
         21,22,23,24,25: begin
              cp = 4'd15; res = 4'd10;
            end
         26,27,28: begin
              cp = 4'd13; res = 4'd12;
            end
         29,30,31: begin
              cp = 4'd14; res = 4'd12;
            end
         32,33,34,35,36,37: begin
              cp = 4'd15; res = 4'd12;
            end
         38,39,40,41: begin
              cp = 4'd14; res = 4'd2;
            end
         42,43,44,45,46,47,48,49,50,51,52,53,54,55,56,57,58,59,60,61,62: begin
              cp = 4'd15; res = 4'd2;
            end
         63,64,65,66,67,68,69,70: begin
              cp = 4'd12; res = 4'd4;
            end
         71,72,73,74,75,76,77: begin
              cp = 4'd13; res = 4'd4;
            end
         78,79,80,81,82,83,84,85: begin
              cp = 4'd14; res = 4'd4;
            end
         86,87,88,89,90,91,92,93,94,95,96,97,98,99,100,101,102,103,104,105,106,107,108,109,110,111,112,113,114,115,116,117,118,119: begin
              cp = 4'd15; res = 4'd4;
            end
         120,121,122,123,124,125,126,127,128: begin
              cp = 4'd13; res = 4'd8;
            end
      endcase
   end
 end
endtask

// end behavioral model

`ifndef XIL_XECLIB
  specify
    (DCLK *> DO) = (100:100:100, 100:100:100);
    (DCLK => DRDY) = (100:100:100, 100:100:100);
    (PSCLK => PSDONE) = (100:100:100, 100:100:100);
    (negedge PWRDWN => (CLKFBSTOPPED +: 0)) = (100:100:100, 100:100:100);
    (negedge PWRDWN => (CLKINSTOPPED +: 0)) = (100:100:100, 100:100:100);
    (negedge PWRDWN => (LOCKED +: 0)) = (100:100:100, 100:100:100);
    (negedge RST => (CLKFBSTOPPED +: 0)) = (100:100:100, 100:100:100);
    (negedge RST => (CLKINSTOPPED +: 0)) = (100:100:100, 100:100:100);
    (negedge RST => (LOCKED +: 0)) = (100:100:100, 100:100:100);
    (posedge PWRDWN => (CLKFBSTOPPED +: 0)) = (100:100:100, 100:100:100);
    (posedge PWRDWN => (CLKINSTOPPED +: 0)) = (100:100:100, 100:100:100);
    (posedge PWRDWN => (LOCKED +: 0)) = (100:100:100, 100:100:100);
    (posedge RST => (CLKFBSTOPPED +: 0)) = (100:100:100, 100:100:100);
    (posedge RST => (CLKINSTOPPED +: 0)) = (100:100:100, 100:100:100);
    (posedge RST => (LOCKED +: 0)) = (100:100:100, 100:100:100);
`ifdef XIL_TIMING
    $period (negedge CLKFBIN, 0:0:0, notifier);
    $period (negedge CLKFBOUT, 0:0:0, notifier);
    $period (negedge CLKFBOUTB, 0:0:0, notifier);
    $period (negedge CLKIN1, 0:0:0, notifier);
    $period (negedge CLKIN2, 0:0:0, notifier);
    $period (negedge CLKOUT0, 0:0:0, notifier);
    $period (negedge CLKOUT0B, 0:0:0, notifier);
    $period (negedge CLKOUT1, 0:0:0, notifier);
    $period (negedge CLKOUT1B, 0:0:0, notifier);
    $period (negedge CLKOUT2, 0:0:0, notifier);
    $period (negedge CLKOUT2B, 0:0:0, notifier);
    $period (negedge CLKOUT3, 0:0:0, notifier);
    $period (negedge CLKOUT3B, 0:0:0, notifier);
    $period (negedge CLKOUT4, 0:0:0, notifier);
    $period (negedge CLKOUT5, 0:0:0, notifier);
    $period (negedge CLKOUT6, 0:0:0, notifier);
    $period (negedge DCLK, 0:0:0, notifier);
    $period (negedge PSCLK, 0:0:0, notifier);
    $period (posedge CLKFBIN, 0:0:0, notifier);
    $period (posedge CLKFBOUT, 0:0:0, notifier);
    $period (posedge CLKFBOUTB, 0:0:0, notifier);
    $period (posedge CLKIN1, 0:0:0, notifier);
    $period (posedge CLKIN2, 0:0:0, notifier);
    $period (posedge CLKOUT0, 0:0:0, notifier);
    $period (posedge CLKOUT0B, 0:0:0, notifier);
    $period (posedge CLKOUT1, 0:0:0, notifier);
    $period (posedge CLKOUT1B, 0:0:0, notifier);
    $period (posedge CLKOUT2, 0:0:0, notifier);
    $period (posedge CLKOUT2B, 0:0:0, notifier);
    $period (posedge CLKOUT3, 0:0:0, notifier);
    $period (posedge CLKOUT3B, 0:0:0, notifier);
    $period (posedge CLKOUT4, 0:0:0, notifier);
    $period (posedge CLKOUT5, 0:0:0, notifier);
    $period (posedge CLKOUT6, 0:0:0, notifier);
    $period (posedge DCLK, 0:0:0, notifier);
    $period (posedge PSCLK, 0:0:0, notifier);
    $setuphold (posedge DCLK, negedge DADDR, 0:0:0, 0:0:0, notifier,,, DCLK_delay, DADDR_delay);
    $setuphold (posedge DCLK, negedge DEN, 0:0:0, 0:0:0, notifier,,, DCLK_delay, DEN_delay);
    $setuphold (posedge DCLK, negedge DI, 0:0:0, 0:0:0, notifier,,, DCLK_delay, DI_delay);
    $setuphold (posedge DCLK, negedge DWE, 0:0:0, 0:0:0, notifier,,, DCLK_delay, DWE_delay);
    $setuphold (posedge DCLK, posedge DADDR, 0:0:0, 0:0:0, notifier,,, DCLK_delay, DADDR_delay);
    $setuphold (posedge DCLK, posedge DEN, 0:0:0, 0:0:0, notifier,,, DCLK_delay, DEN_delay);
    $setuphold (posedge DCLK, posedge DI, 0:0:0, 0:0:0, notifier,,, DCLK_delay, DI_delay);
    $setuphold (posedge DCLK, posedge DWE, 0:0:0, 0:0:0, notifier,,, DCLK_delay, DWE_delay);
    $setuphold (posedge PSCLK, negedge PSEN, 0:0:0, 0:0:0, notifier,,, PSCLK_delay, PSEN_delay);
    $setuphold (posedge PSCLK, negedge PSINCDEC, 0:0:0, 0:0:0, notifier,,, PSCLK_delay, PSINCDEC_delay);
    $setuphold (posedge PSCLK, posedge PSEN, 0:0:0, 0:0:0, notifier,,, PSCLK_delay, PSEN_delay);
    $setuphold (posedge PSCLK, posedge PSINCDEC, 0:0:0, 0:0:0, notifier,,, PSCLK_delay, PSINCDEC_delay);
    $width (negedge CLKIN1, 0:0:0, 0, notifier);
    $width (negedge CLKIN2, 0:0:0, 0, notifier);
    $width (negedge DCLK, 0:0:0, 0, notifier);
    $width (negedge PSCLK, 0:0:0, 0, notifier);
    $width (negedge PWRDWN, 0:0:0, 0, notifier);
    $width (negedge RST, 0:0:0, 0, notifier);
    $width (posedge CLKIN1, 0:0:0, 0, notifier);
    $width (posedge CLKIN2, 0:0:0, 0, notifier);
    $width (posedge DCLK, 0:0:0, 0, notifier);
    $width (posedge PSCLK, 0:0:0, 0, notifier);
    $width (posedge PWRDWN, 0:0:0, 0, notifier);
    $width (posedge RST, 0:0:0, 0, notifier);
`endif
    specparam PATHPULSE$ = 0;
  endspecify
`endif
endmodule

`endcelldefine
