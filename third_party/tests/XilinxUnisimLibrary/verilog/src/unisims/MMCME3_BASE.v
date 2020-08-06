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
// /___/   /\      Filename    : MMCME3_BASE.v
// \   \  /  \
//  \___\/\___\
//
///////////////////////////////////////////////////////////////////////////////
//  Revision:
//  10/22/2014 808642 - Added #1 to $finish
//  End Revision:
///////////////////////////////////////////////////////////////////////////////

`timescale 1 ps / 1 ps

`celldefine

module MMCME3_BASE #(
`ifdef XIL_TIMING
  parameter LOC = "UNPLACED",
`endif
  parameter BANDWIDTH = "OPTIMIZED",
  parameter real CLKFBOUT_MULT_F = 5.000,
  parameter real CLKFBOUT_PHASE = 0.000,
  parameter real CLKIN1_PERIOD = 0.000,
  parameter real CLKOUT0_DIVIDE_F = 1.000,
  parameter real CLKOUT0_DUTY_CYCLE = 0.500,
  parameter real CLKOUT0_PHASE = 0.000,
  parameter integer CLKOUT1_DIVIDE = 1,
  parameter real CLKOUT1_DUTY_CYCLE = 0.500,
  parameter real CLKOUT1_PHASE = 0.000,
  parameter integer CLKOUT2_DIVIDE = 1,
  parameter real CLKOUT2_DUTY_CYCLE = 0.500,
  parameter real CLKOUT2_PHASE = 0.000,
  parameter integer CLKOUT3_DIVIDE = 1,
  parameter real CLKOUT3_DUTY_CYCLE = 0.500,
  parameter real CLKOUT3_PHASE = 0.000,
  parameter CLKOUT4_CASCADE = "FALSE",
  parameter integer CLKOUT4_DIVIDE = 1,
  parameter real CLKOUT4_DUTY_CYCLE = 0.500,
  parameter real CLKOUT4_PHASE = 0.000,
  parameter integer CLKOUT5_DIVIDE = 1,
  parameter real CLKOUT5_DUTY_CYCLE = 0.500,
  parameter real CLKOUT5_PHASE = 0.000,
  parameter integer CLKOUT6_DIVIDE = 1,
  parameter real CLKOUT6_DUTY_CYCLE = 0.500,
  parameter real CLKOUT6_PHASE = 0.000,
  parameter integer DIVCLK_DIVIDE = 1,
  parameter [0:0] IS_CLKFBIN_INVERTED = 1'b0,
  parameter [0:0] IS_CLKIN1_INVERTED = 1'b0,
  parameter [0:0] IS_PWRDWN_INVERTED = 1'b0,
  parameter [0:0] IS_RST_INVERTED = 1'b0,
  parameter real REF_JITTER1 = 0.010,
  parameter STARTUP_WAIT = "FALSE"
)(
  output CLKFBOUT,
  output CLKFBOUTB,
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
  output LOCKED,

  input CLKFBIN,
  input CLKIN1,
  input PWRDWN,
  input RST
);

// define constants
  localparam MODULE_NAME = "MMCME3_BASE";

  reg trig_attr = 1'b0;
  localparam [0:0] IS_CLKFBIN_INVERTED_REG = IS_CLKFBIN_INVERTED;
  localparam [0:0] IS_CLKIN1_INVERTED_REG = IS_CLKIN1_INVERTED;
  localparam [0:0] IS_PWRDWN_INVERTED_REG = IS_PWRDWN_INVERTED;
  localparam [0:0] IS_RST_INVERTED_REG = IS_RST_INVERTED;


`ifdef XIL_ATTR_TEST
  reg attr_test = 1'b1;
`else
  reg attr_test = 1'b0;
`endif

  reg attr_err = 1'b0;

  wire CLKFBIN_in;
  wire CLKIN1_in;
  wire PWRDWN_in;
  wire RST_in;

  assign CLKFBIN_in = (CLKFBIN !== 1'bz) && (CLKFBIN ^ IS_CLKFBIN_INVERTED_REG); // rv 0
  assign CLKIN1_in = (CLKIN1 !== 1'bz) && (CLKIN1 ^ IS_CLKIN1_INVERTED_REG); // rv 0
  assign PWRDWN_in = (PWRDWN !== 1'bz) && (PWRDWN ^ IS_PWRDWN_INVERTED_REG); // rv 0
  assign RST_in = (RST !== 1'bz) && (RST ^ IS_RST_INVERTED_REG); // rv 0

  initial begin
    #1;
    trig_attr = ~trig_attr;
  end

`ifndef XIL_XECLIB
  always @ (trig_attr) begin
    #1;
    if ((attr_test == 1'b1) ||
        ((IS_CLKFBIN_INVERTED_REG !== 1'b0) && (IS_CLKFBIN_INVERTED_REG !== 1'b1))) begin
      $display("Error: [Unisim %s-142] IS_CLKFBIN_INVERTED attribute is set to %b.  Legal values for this attribute are 1'b0 to 1'b1. Instance: %m", MODULE_NAME, IS_CLKFBIN_INVERTED_REG);
      attr_err = 1'b1;
    end

    if ((attr_test == 1'b1) ||
        ((IS_CLKIN1_INVERTED_REG !== 1'b0) && (IS_CLKIN1_INVERTED_REG !== 1'b1))) begin
      $display("Error: [Unisim %s-143] IS_CLKIN1_INVERTED attribute is set to %b.  Legal values for this attribute are 1'b0 to 1'b1. Instance: %m", MODULE_NAME, IS_CLKIN1_INVERTED_REG);
      attr_err = 1'b1;
    end

    if ((attr_test == 1'b1) ||
        ((IS_PWRDWN_INVERTED_REG !== 1'b0) && (IS_PWRDWN_INVERTED_REG !== 1'b1))) begin
      $display("Error: [Unisim %s-148] IS_PWRDWN_INVERTED attribute is set to %b.  Legal values for this attribute are 1'b0 to 1'b1. Instance: %m", MODULE_NAME, IS_PWRDWN_INVERTED_REG);
      attr_err = 1'b1;
    end

    if ((attr_test == 1'b1) ||
        ((IS_RST_INVERTED_REG !== 1'b0) && (IS_RST_INVERTED_REG !== 1'b1))) begin
      $display("Error: [Unisim %s-149] IS_RST_INVERTED attribute is set to %b.  Legal values for this attribute are 1'b0 to 1'b1. Instance: %m", MODULE_NAME, IS_RST_INVERTED_REG);
      attr_err = 1'b1;
    end

    if (attr_err == 1'b1) #1 $finish;

end
`endif

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

  wire CDDCDONE;
  wire DRDY;
  wire PSDONE;
  wire CLKFBSTOPPED;
  wire CLKINSTOPPED;
  wire [15:0] DO;
  MMCME3_ADV #(
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
       .CDDCDONE (CDDCDONE),
       .CLKFBOUT (CLKFBOUT),
       .CLKFBOUTB (CLKFBOUTB),
       .CLKFBSTOPPED(CLKFBSTOPPED),
       .CLKINSTOPPED(CLKINSTOPPED),
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
       .DO (DO),
       .DRDY (DRDY),
       .LOCKED (LOCKED),
       .PSDONE(PSDONE),
       .CDDCREQ (1'b0),
       .CLKFBIN (CLKFBIN_in),
       .CLKIN1 (CLKIN1_in),
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
       .PWRDWN(PWRDWN_in),
       .RST (RST_in)
    );

`ifndef XIL_XECLIB
`ifdef XIL_TIMING
  reg notifier;
`endif

  specify
    (negedge RST => (LOCKED +: 0)) = (100:100:100, 100:100:100);
    (posedge RST => (LOCKED +: 0)) = (100:100:100, 100:100:100);
`ifdef XIL_TIMING
    $period (negedge CLKFBIN, 0:0:0, notifier);
    $period (negedge CLKFBOUT, 0:0:0, notifier);
    $period (negedge CLKFBOUTB, 0:0:0, notifier);
    $period (negedge CLKIN1, 0:0:0, notifier);
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
    $period (posedge CLKFBIN, 0:0:0, notifier);
    $period (posedge CLKFBOUT, 0:0:0, notifier);
    $period (posedge CLKFBOUTB, 0:0:0, notifier);
    $period (posedge CLKIN1, 0:0:0, notifier);
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
    $width (negedge CLKIN1, 0:0:0, 0, notifier);
    $width (negedge PWRDWN, 0:0:0, 0, notifier);
    $width (negedge RST, 0:0:0, 0, notifier);
    $width (posedge CLKIN1, 0:0:0, 0, notifier);
    $width (posedge PWRDWN, 0:0:0, 0, notifier);
    $width (posedge RST, 0:0:0, 0, notifier);
`endif
    specparam PATHPULSE$ = 0;
  endspecify
`endif
endmodule

`endcelldefine
