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
// \   \   \/      Version     : 2017.1
//  \   \          Description : Xilinx Unified Simulation Library Component
//  /   /                        Base Mixed Mode Clock Manager (MMCM)
// /___/   /\      Filename    : MMCME2_BASE.v
// \   \  /  \
//  \___\/\___\
//
///////////////////////////////////////////////////////////////////////////////
//  Revision:
//  05/27/10 - Initial version
//  End Revision:
///////////////////////////////////////////////////////////////////////////////

`timescale 1 ps / 1 ps

`celldefine

module MMCME2_BASE (
  CLKFBOUT,
  CLKFBOUTB,
  CLKOUT0,
  CLKOUT0B,
  CLKOUT1,
  CLKOUT1B,
  CLKOUT2,
  CLKOUT2B,
  CLKOUT3,
  CLKOUT3B,
  CLKOUT4,
  CLKOUT5,
  CLKOUT6,
  LOCKED,
  CLKFBIN,
  CLKIN1,
  PWRDWN,
  RST
);

  parameter BANDWIDTH = "OPTIMIZED";
  parameter real CLKFBOUT_MULT_F = 5.000;
  parameter real CLKFBOUT_PHASE = 0.000;
  parameter real CLKIN1_PERIOD = 0.000;
  parameter real CLKOUT0_DIVIDE_F = 1.000;
  parameter real CLKOUT0_DUTY_CYCLE = 0.500;
  parameter real CLKOUT0_PHASE = 0.000;
  parameter integer CLKOUT1_DIVIDE = 1;
  parameter real CLKOUT1_DUTY_CYCLE = 0.500;
  parameter real CLKOUT1_PHASE = 0.000;
  parameter integer CLKOUT2_DIVIDE = 1;
  parameter real CLKOUT2_DUTY_CYCLE = 0.500;
  parameter real CLKOUT2_PHASE = 0.000;
  parameter integer CLKOUT3_DIVIDE = 1;
  parameter real CLKOUT3_DUTY_CYCLE = 0.500;
  parameter real CLKOUT3_PHASE = 0.000;
  parameter CLKOUT4_CASCADE = "FALSE";
  parameter integer CLKOUT4_DIVIDE = 1;
  parameter real CLKOUT4_DUTY_CYCLE = 0.500;
  parameter real CLKOUT4_PHASE = 0.000;
  parameter integer CLKOUT5_DIVIDE = 1;
  parameter real CLKOUT5_DUTY_CYCLE = 0.500;
  parameter real CLKOUT5_PHASE = 0.000;
  parameter integer CLKOUT6_DIVIDE = 1;
  parameter real CLKOUT6_DUTY_CYCLE = 0.500;
  parameter real CLKOUT6_PHASE = 0.000;
  parameter integer DIVCLK_DIVIDE = 1;
  parameter real REF_JITTER1 = 0.010;
  parameter STARTUP_WAIT = "FALSE";

  `ifdef XIL_TIMING

    parameter LOC = "UNPLACED";

  `endif

  output CLKFBOUT;
  output CLKFBOUTB;
  output CLKOUT0;
  output CLKOUT0B;
  output CLKOUT1;
  output CLKOUT1B;
  output CLKOUT2;
  output CLKOUT2B;
  output CLKOUT3;
  output CLKOUT3B;
  output CLKOUT4;
  output CLKOUT5;
  output CLKOUT6;
  output LOCKED;

  input CLKFBIN;
  input CLKIN1;
  input PWRDWN;
  input RST;

// define constants
  localparam MODULE_NAME = "MMCME2_BASE";

  wire OPEN_DRDY;
  wire OPEN_PSDONE;
  wire OPEN_FBS;
  wire OPEN_INS;
  wire [15:0] OPEN_DO;

  MMCME2_ADV #(
       .BANDWIDTH(BANDWIDTH),
       .CLKFBOUT_MULT_F(CLKFBOUT_MULT_F),
       .CLKFBOUT_PHASE(CLKFBOUT_PHASE),
       .CLKIN1_PERIOD(CLKIN1_PERIOD),
       .CLKIN2_PERIOD(10),
       .CLKOUT0_DIVIDE_F(CLKOUT0_DIVIDE_F),
       .CLKOUT0_DUTY_CYCLE(CLKOUT0_DUTY_CYCLE),
       .CLKOUT0_PHASE(CLKOUT0_PHASE),
       .CLKOUT1_DIVIDE(CLKOUT1_DIVIDE),
       .CLKOUT1_DUTY_CYCLE(CLKOUT1_DUTY_CYCLE),
       .CLKOUT1_PHASE(CLKOUT1_PHASE),
       .CLKOUT2_DIVIDE(CLKOUT2_DIVIDE),
       .CLKOUT2_DUTY_CYCLE(CLKOUT2_DUTY_CYCLE),
       .CLKOUT2_PHASE(CLKOUT2_PHASE),
       .CLKOUT3_DIVIDE(CLKOUT3_DIVIDE),
       .CLKOUT3_DUTY_CYCLE(CLKOUT3_DUTY_CYCLE),
       .CLKOUT3_PHASE(CLKOUT3_PHASE),
       .CLKOUT4_CASCADE(CLKOUT4_CASCADE),
       .CLKOUT4_DIVIDE(CLKOUT4_DIVIDE),
       .CLKOUT4_DUTY_CYCLE(CLKOUT4_DUTY_CYCLE),
       .CLKOUT4_PHASE(CLKOUT4_PHASE),
       .CLKOUT5_DIVIDE(CLKOUT5_DIVIDE),
       .CLKOUT5_DUTY_CYCLE(CLKOUT5_DUTY_CYCLE),
       .CLKOUT5_PHASE(CLKOUT5_PHASE),
       .CLKOUT6_DIVIDE(CLKOUT6_DIVIDE),
       .CLKOUT6_DUTY_CYCLE(CLKOUT6_DUTY_CYCLE),
       .CLKOUT6_PHASE(CLKOUT6_PHASE),
       .DIVCLK_DIVIDE(DIVCLK_DIVIDE),
       .REF_JITTER1(REF_JITTER1),
       .STARTUP_WAIT(STARTUP_WAIT)
      ) mmcm_adv_1 (
       .CLKFBOUT (CLKFBOUT),
       .CLKFBOUTB (CLKFBOUTB),
       .CLKFBSTOPPED(OPEN_FBS),
       .CLKINSTOPPED(OPEN_INS),
       .CLKOUT0 (CLKOUT0),
       .CLKOUT0B (CLKOUT0B),
       .CLKOUT1 (CLKOUT1),
       .CLKOUT1B (CLKOUT1B),
       .CLKOUT2 (CLKOUT2),
       .CLKOUT2B (CLKOUT2B),
       .CLKOUT3 (CLKOUT3),
       .CLKOUT3B (CLKOUT3B),
       .CLKOUT4 (CLKOUT4),
       .CLKOUT5 (CLKOUT5),
       .CLKOUT6 (CLKOUT6),
       .DO (OPEN_DO),
       .DRDY (OPEN_DRDY),
       .LOCKED (LOCKED),
       .PSDONE(OPEN_PSDONE),
       .CLKFBIN (CLKFBIN),
       .CLKIN1 (CLKIN1),
       .CLKIN2 (1'b0),
       .CLKINSEL(1'b1),
       .DADDR (7'b0),
       .DCLK (1'b0),
       .DEN (1'b0),
       .DI (16'b0),
       .DWE (1'b0),
       .PSCLK(1'b0),
       .PSEN(1'b0),
       .PSINCDEC(1'b0),
       .PWRDWN(PWRDWN),
       .RST (RST)
    );
endmodule

`endcelldefine
