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
// \   \   \/      Version     : 2017.4
//  \   \          Description : Xilinx Unified Simulation Library Component
//  /   /                        Advanced Phase-Locked Loop (PLL)
// /___/   /\      Filename    : PLLE4_ADV.v
// \   \  /  \
//  \___\/\___\
//
///////////////////////////////////////////////////////////////////////////////
//  Revision:
//  02/22/2013 700625 - update PLLE3 for yml changes
//  02/28/2013 703674 - update vco_half attribute
//  03/25/2013 PLLE3 sync5 changes
//  04/04/2013 709484 - add PFD check
//  04/02/2013 709723 - fix Lock for lost clock
//  04/08/2013 709729 - Fix clkoutxiphy for CLKIN mode
//  04/09/2013 709725 - Fix clkout0 frequency after reset
//  04/09/2013 709726 - Fix clkout0 frequency
//  04/12/2013 Invertible pin changes
//  04/16/2013 Writer and invertible pin changes
//  04/22/2013 713959 - clkoutphy frequency fix after reset
//  10/22/2014 808642 - Added #1 to $finish
//  End Revision:
///////////////////////////////////////////////////////////////////////////////

`timescale 1 ps / 1 ps

`celldefine

module PLLE4_ADV #(
`ifdef XIL_TIMING
  parameter LOC = "UNPLACED",
  parameter real CLKIN_FREQ_MAX = 1066.000,
  parameter real CLKIN_FREQ_MIN = 70.000,
  parameter real CLKPFD_FREQ_MAX = 667.500,
  parameter real CLKPFD_FREQ_MIN = 70.000,
  parameter real VCOCLK_FREQ_MAX = 1500.000,
  parameter real VCOCLK_FREQ_MIN = 750.000,
`endif
  parameter integer CLKFBOUT_MULT = 5,
  parameter real CLKFBOUT_PHASE = 0.000,
  parameter real CLKIN_PERIOD = 0.000,
  parameter integer CLKOUT0_DIVIDE = 1,
  parameter real CLKOUT0_DUTY_CYCLE = 0.500,
  parameter real CLKOUT0_PHASE = 0.000,
  parameter integer CLKOUT1_DIVIDE = 1,
  parameter real CLKOUT1_DUTY_CYCLE = 0.500,
  parameter real CLKOUT1_PHASE = 0.000,
  parameter CLKOUTPHY_MODE = "VCO_2X",
  parameter COMPENSATION = "AUTO",
  parameter integer DIVCLK_DIVIDE = 1,
  parameter [0:0] IS_CLKFBIN_INVERTED = 1'b0,
  parameter [0:0] IS_CLKIN_INVERTED = 1'b0,
  parameter [0:0] IS_PWRDWN_INVERTED = 1'b0,
  parameter [0:0] IS_RST_INVERTED = 1'b0,
  parameter real REF_JITTER = 0.010,
  parameter STARTUP_WAIT = "FALSE"
)(
  output CLKFBOUT,
  output CLKOUT0,
  output CLKOUT0B,
  output CLKOUT1,
  output CLKOUT1B,
  output CLKOUTPHY,
  output [15:0] DO,
  output DRDY,
  output LOCKED,

  input CLKFBIN,
  input CLKIN,
  input CLKOUTPHYEN,
  input [6:0] DADDR,
  input DCLK,
  input DEN,
  input [15:0] DI,
  input DWE,
  input PWRDWN,
  input RST
);

`ifndef XIL_TIMING
  localparam real CLKIN_FREQ_MAX = 1066.000;
  localparam real CLKIN_FREQ_MIN = 70.000;
  localparam real CLKPFD_FREQ_MAX = 667.500;
  localparam real CLKPFD_FREQ_MIN = 70.000;
  localparam real VCOCLK_FREQ_MAX = 1500.000;
  localparam real VCOCLK_FREQ_MIN = 750.000;
`endif

// define constants
  localparam MODULE_NAME = "PLLE4_ADV";

// Parameter encodings and registers
  localparam CLKOUTPHY_MODE_VCO = 1;
  localparam CLKOUTPHY_MODE_VCO_2X = 0;
  localparam CLKOUTPHY_MODE_VCO_HALF = 2;
  localparam COMPENSATION_AUTO = 0;
  localparam COMPENSATION_BUF_IN = 1;
  localparam COMPENSATION_INTERNAL = 3;
  localparam COMPENSATION_PHY_ALIGN = 2;
  localparam STARTUP_WAIT_FALSE = 0;
  localparam STARTUP_WAIT_TRUE = 1;

  reg trig_attr;
// include dynamic registers - XILINX test only
`ifdef XIL_DR
  `include "PLLE4_ADV_dr.v"
`else
  localparam [4:0] CLKFBOUT_MULT_REG = CLKFBOUT_MULT;
  localparam real CLKFBOUT_PHASE_REG = CLKFBOUT_PHASE;
  localparam real CLKIN_FREQ_MAX_REG = CLKIN_FREQ_MAX;
  localparam real CLKIN_FREQ_MIN_REG = CLKIN_FREQ_MIN;
  localparam real CLKIN_PERIOD_REG = CLKIN_PERIOD;
  localparam [7:0] CLKOUT0_DIVIDE_REG = CLKOUT0_DIVIDE;
  localparam real CLKOUT0_DUTY_CYCLE_REG = CLKOUT0_DUTY_CYCLE;
  localparam real CLKOUT0_PHASE_REG = CLKOUT0_PHASE;
  localparam [7:0] CLKOUT1_DIVIDE_REG = CLKOUT1_DIVIDE;
  localparam real CLKOUT1_DUTY_CYCLE_REG = CLKOUT1_DUTY_CYCLE;
  localparam real CLKOUT1_PHASE_REG = CLKOUT1_PHASE;
  localparam [64:1] CLKOUTPHY_MODE_REG = CLKOUTPHY_MODE;
  localparam real CLKPFD_FREQ_MAX_REG = CLKPFD_FREQ_MAX;
  localparam real CLKPFD_FREQ_MIN_REG = CLKPFD_FREQ_MIN;
  localparam [72:1] COMPENSATION_REG = COMPENSATION;
  localparam [3:0] DIVCLK_DIVIDE_REG = DIVCLK_DIVIDE;
  localparam [0:0] IS_CLKFBIN_INVERTED_REG = IS_CLKFBIN_INVERTED;
  localparam [0:0] IS_CLKIN_INVERTED_REG = IS_CLKIN_INVERTED;
  localparam [0:0] IS_PWRDWN_INVERTED_REG = IS_PWRDWN_INVERTED;
  localparam [0:0] IS_RST_INVERTED_REG = IS_RST_INVERTED;
  localparam real REF_JITTER_REG = REF_JITTER;
  localparam [40:1] STARTUP_WAIT_REG = STARTUP_WAIT;
  localparam real VCOCLK_FREQ_MAX_REG = VCOCLK_FREQ_MAX;
  localparam real VCOCLK_FREQ_MIN_REG = VCOCLK_FREQ_MIN;
`endif

  wire [2:0] COMPENSATION_BIN;
  reg attr_test;
  reg attr_err;
  tri0 glblGSR = glbl.GSR;

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

  localparam VCOCLK_FREQ_TARGET = 1200;
  localparam M_MIN = 2;
  localparam M_MAX = 21;
  localparam real VF_MAX = 1500.000;
  localparam real VF_MIN = 750.000;
  localparam D_MIN = 1;
  localparam D_MAX = 15;
//  localparam O_MIN = 1; // not used
  localparam O_MAX = 256;
  localparam O_MAX_HT_LT = 128; // change from 64
  localparam REF_CLK_JITTER_MAX = 1000;
  localparam OSC_P2 = 250;

  integer nBandwidth_HIGH=0;
  integer nBandwidth_LOW=1;
  integer nBandwidth_OPTIMIZED=2;

  tri1 p_up;
  reg [160:0] tmp_string;
  reg chk_ok;
  reg init_chk;
  real  clkin_chk_t1, clkin_chk_t2;
  real  clkin_chk_t1_r, clkin_chk_t2_r;
  integer   clkin_chk_t1_i, clkin_chk_t2_i;
  real    clkvco_freq_init_chk;
  real    clkpfd_freq_init_chk;
  wire [1:0] xiphy_mode;

  wire [15:0] do_out;
  wire [15:0] di_in;
  wire [6:0] daddr_in;
  reg [15:0] do_out1;
  integer clkfb_div_fint;

  wire locked_out;
  reg locked_out1;
  reg locked_out_tmp;

  reg [3:0] pll_cp, pll_res;
  reg [1:0] pll_lfhf;
  reg [1:0] pll_cpres = 2'b01;
  reg [6:0] daddr_lat;
  reg valid_daddr;
  reg drdy_out, drdy_out1;
  reg drp_lock;
  reg [2:0] drp_lock_lat = 3'b100;
  reg [2:0] drp_lock_lat_cnt;
  reg [15:0] dr_sram [127:0];
  reg [4:0] drp_lock_ref_dly;
  reg [4:0] drp_lock_fb_dly;
  reg [9:0] drp_lock_cnt;
  reg [9:0] drp_unlock_cnt;
  reg [9:0] drp_lock_sat_high;

  integer  period_vco_max, period_vco_min;
  integer  period_vco_target, period_vco_target_half;
  integer  clkin_lock_cnt;
  integer clkout_en_time, locked_en_time, lock_cnt_max;
  integer pll_lock_time, lock_period_time;
  integer md_product, m_product, m_product2;
  integer clkout_en_val;
  reg clkout0_out, clkout1_out;

  reg [7:0] clk0_ht, clk0_lt;
  reg [7:0] clk1_ht, clk1_lt;
  reg clk0_edge, clk1_edge;
  reg clk0_nocnt, clk1_nocnt;

  reg rst_in = 1'b0;
  integer  clkin_period_tmp;
  integer  clkin_period [4:0];
  reg lock_period;
  reg pll_locked_tm, unlock_recover;
  reg clkpll_jitter_unlock = 1'b0;
  integer  clkin_jit;
  integer pchk_tmp1, pchk_tmp2;
  integer period_avg, period_fb;
  wire clkin_in,clkfb_in;
  reg clkout_en, clkout_en0_tmp, clkout_en0_tmp1=0, clkout_en0, clkout_en1;
  wire pll_unlock, pll_unlock1;
  reg pll_locked_tmp1, pll_locked_tmp2, pll_locked_tmp2_dly;
  time clkin_edge, delay_edge;
  time fb_delay, clkvco_delay, val_tmp, dly_tmp, fbm1_comp_delay;
  time dly_tmp1;
  integer dly_tmp_int;
  reg fb_delay_found, fb_delay_found_tmp;
  real fb_delay_max;
  integer  period_vco_mf;
  integer  period_vco_rm, period_vco_cmp_cnt, clkvco_rm_cnt;
  integer  period_vco_cmp_flag;
  integer  period_vco, period_vco_half, period_vco_half1, period_vco_half_rm;
  integer  period_vco_half_rm1, period_vco_half_rm2;
  time pll_locked_delay, clkin_dly_t;
  reg clkpll = 1'b0;
  reg clkpll_tmp1 = 1'b0;
  reg clkvco_lk = 1'b0, clkvco_lk_tmp = 1'b0, clkvco = 1'b0, clkvco_by2 = 1'b0, clkvco_2x = 1'b0;
  reg clkvco_by8 = 1'b0;
  integer i, ik2, ik3, ik4, j;
  reg vcoflag = 1'b0;
  integer clkout_en_t;
  reg clk_osc=1'b0, clkin_p=1'b0, clkfb_p=1'b0;
  reg clkinstopped_out; 
  reg clkfbstopped_out;
  integer clkin_lost_cnt, clkfb_lost_cnt;
  integer clkin_lost_val, clkfb_lost_val;
  reg clkinstopped_out_dly = 0;

  reg pwron_int;
  reg clkfb_tst = 1'b0;
  reg [7:0] clkind_div;
  reg [2:0] clkout_mux;
  //reg [2:0] clk0pm_sel, clk1pm_sel, clkfbm1pm_sel;
  reg [7:0] clkfbtmp_divi, clkfbtmp_hti, clkfbtmp_lti;
  reg [7:0] clkfbm1_ht1, clkfbm1_cnt, clkfbm1_div, clkfbm1_div1;
  reg [7:0] clkfbm2_ht1, clkfbm2_cnt, clkfbm2_div, clkfbm2_div1;
  reg [7:0] clkind_divi, clkind_div1, clkind_cnt, clkind_ht1;
  reg clkfbtmp_nocnti;
  reg clkind_edgei, clkind_nocnti;
  reg clkind_out, clkind_out_tmp;
  reg [6:0] clkfbm1_ht, clkfbm1_lt;
  reg [6:0] clkfbin_ht, clkfbin_lt;
  reg [7:0] clkind_ht, clkind_lt;
  reg [7:0] clkind_hti, clkind_lti;
  reg clkfbm1_nocnt, clkind_nocnt;
  reg clkfbm1_edge, clkind_edge;
  reg clkfbin_edge, clkfbin_nocnt;
  reg clkfbm1_nf_out;
  
  integer  period_vco1;
  integer  period_vco2;
  reg clk0_out;
  reg clk1_out;
  reg clkfb_out;
  wire clkfbm1_out;
  reg clkfbm2_out;
  reg [5:0] clk0_dly_cnt, clkout0_dly;
  reg [5:0] clk1_dly_cnt, clkout1_dly;
  reg [5:0] clkfbm1_dly_cnt, clkfbm1_dly;
  reg [8:0] clk0_ht1, clk0_cnt, clk0_div, clk0_div1;
  reg [8:0] clk1_ht1, clk1_cnt, clk1_div, clk1_div1;
  wire init_trig, clk0in, clk1in;
 
  wire clkoutxiphy_int;
  wire xiphyen_in;
  reg  xiphyen_sync=1'b0;
  reg  xiphyen_sync1=1'b0;
  reg  xiphyen_sync2=1'b0;
  reg  [1:0] clkvco_cnt=2'b00;

  wire DCLK_delay;
  wire DEN_delay;
  wire DWE_delay;
  wire [15:0] DI_delay;
  wire [6:0] DADDR_delay;

  wire dwe_in;
  wire den_in;
  wire dclk_in;

`ifdef XIL_TIMING
  reg notifier;
`endif

`ifndef XIL_TIMING
  assign DCLK_delay = DCLK;

  assign DADDR_delay = DADDR;
  assign DEN_delay = DEN;
  assign DI_delay = DI;
  assign DWE_delay = DWE;
`endif

  wire CLKFBIN_int;
  wire startup_wait_sig;
  wire clkfbin_sel;
  wire pwrdwn_in;
  wire rst_input_r;
  wire glock;
  wire pwrdwn_in1;
  wire rst_input;
  wire clkfbm1in;
  wire clk0ps_en, clk1ps_en;
  wire clkfbm1ps_en;
  reg drp_updt = 1'b0;
  assign clkfb_in =  CLKFBIN ^ IS_CLKFBIN_INVERTED_REG;
  assign clkin_in =  CLKIN ^ IS_CLKIN_INVERTED_REG;
  assign xiphyen_in = CLKOUTPHYEN;  
  assign daddr_in = DADDR_delay;
  assign di_in = DI_delay;
  assign dwe_in = DWE_delay;
  assign den_in = DEN_delay;
  assign dclk_in = DCLK_delay;
  assign pwrdwn_in =  PWRDWN ^ IS_PWRDWN_INVERTED_REG;
  assign rst_input_r =  RST ^ IS_RST_INVERTED_REG;
  assign LOCKED = locked_out1;
  assign DRDY = drdy_out1;
  assign DO = do_out1;

  always @(locked_out_tmp)
    locked_out1 =  locked_out_tmp;
  always @(pll_locked_tmp2)
      pll_locked_tmp2_dly =  pll_locked_tmp2;
  always @(drdy_out)
    drdy_out1 =  drdy_out;
  always @(do_out)
    do_out1 =  do_out;
 // `endif //  `ifndef XIL_TIMING

  assign COMPENSATION_BIN =
    (COMPENSATION_REG == "AUTO") ? COMPENSATION_AUTO :
    (COMPENSATION_REG == "BUF_IN") ? COMPENSATION_BUF_IN :
    (COMPENSATION_REG == "INTERNAL") ? COMPENSATION_INTERNAL :
    (COMPENSATION_REG == "PHY_ALIGN") ? COMPENSATION_PHY_ALIGN :
     COMPENSATION_AUTO;

  assign xiphy_mode =
    (CLKOUTPHY_MODE_REG == "VCO_2X") ? CLKOUTPHY_MODE_VCO_2X :
    (CLKOUTPHY_MODE_REG == "VCO") ? CLKOUTPHY_MODE_VCO :
    (CLKOUTPHY_MODE_REG == "VCO_HALF") ? CLKOUTPHY_MODE_VCO_HALF :
     CLKOUTPHY_MODE_VCO_2X;

  assign startup_wait_sig =
    (STARTUP_WAIT_REG == "FALSE") ? STARTUP_WAIT_FALSE :
    (STARTUP_WAIT_REG == "TRUE") ? STARTUP_WAIT_TRUE :
     STARTUP_WAIT_FALSE;

  initial begin
    #1;
    trig_attr = ~trig_attr;
    if ($realtime == 0) begin
      $display ("Error: [Unisim %s-1] Simulator resolution is set to a value greater than 1 ps. ", MODULE_NAME);
      $display ("The simulator resolution must be set to 1ps or smaller. Instance %m");
      #1 $finish;
    end
  end

  always @ (trig_attr) begin
    #1;
    if ((attr_test == 1'b1) ||
        ((CLKFBOUT_MULT_REG < M_MIN) || (CLKFBOUT_MULT_REG > M_MAX))) begin
      $display("Error: [Unisim %s-102] CLKFBOUT_MULT attribute is set to %d.  Legal values for this attribute are %d to %d. Instance: %m", MODULE_NAME, CLKFBOUT_MULT_REG, M_MIN, M_MAX);
      attr_err = 1'b1;
    end

    if ((attr_test == 1'b1) ||
        (CLKFBOUT_PHASE_REG < -360.000 || CLKFBOUT_PHASE_REG > 360.000)) begin
      $display("Error: [Unisim %s-103] CLKFBOUT_PHASE attribute is set to %f.  Legal values for this attribute are -360.000 to 360.000. Instance: %m", MODULE_NAME, CLKFBOUT_PHASE_REG);
      attr_err = 1'b1;
    end

    if ((attr_test == 1'b1) ||
        (CLKIN_FREQ_MAX_REG < 800.000 || CLKIN_FREQ_MAX_REG > 1066.000)) begin
      $display("Error: [Unisim %s-107] CLKIN_FREQ_MAX attribute is set to %f.  Legal values for this attribute are 800.000 to 1066.000. Instance: %m", MODULE_NAME, CLKIN_FREQ_MAX_REG);
      attr_err = 1'b1;
    end

    if ((attr_test == 1'b1) ||
        (CLKIN_FREQ_MIN_REG < 70.000 || CLKIN_FREQ_MIN_REG > 70.000)) begin
      $display("Error: [Unisim %s-108] CLKIN_FREQ_MIN attribute is set to %f.  Legal values for this attribute are 70.000 to 70.000. Instance: %m", MODULE_NAME, CLKIN_FREQ_MIN_REG);
      attr_err = 1'b1;
    end

    if ((attr_test == 1'b1) ||
        (CLKIN_PERIOD_REG < 0.000 || CLKIN_PERIOD_REG > 14.286)) begin
      $display("Error: [Unisim %s-105] CLKIN_PERIOD attribute is set to %f.  Legal values for this attribute are 0.000 to 14.286. Instance: %m", MODULE_NAME, CLKIN_PERIOD_REG);
      attr_err = 1'b1;
    end

    if ((attr_test == 1'b1) ||
        ((CLKOUT0_DIVIDE_REG < 1) || (CLKOUT0_DIVIDE_REG > 128))) begin
      $display("Error: [Unisim %s-106] CLKOUT0_DIVIDE attribute is set to %d.  Legal values for this attribute are 1 to 128. Instance: %m", MODULE_NAME, CLKOUT0_DIVIDE_REG);
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
        ((CLKOUTPHY_MODE_REG != "VCO_2X") &&
         (CLKOUTPHY_MODE_REG != "VCO") &&
         (CLKOUTPHY_MODE_REG != "VCO_HALF"))) begin
      $display("Error: [Unisim %s-112] CLKOUTPHY_MODE attribute is set to %s.  Legal values for this attribute are VCO_2X, VCO or VCO_HALF. Instance: %m", MODULE_NAME, CLKOUTPHY_MODE_REG);
      attr_err = 1'b1;
    end

    if ((attr_test == 1'b1) ||
        (CLKPFD_FREQ_MAX_REG < 600.000 || CLKPFD_FREQ_MAX_REG > 667.500)) begin
      $display("Error: [Unisim %s-138] CLKPFD_FREQ_MAX attribute is set to %f.  Legal values for this attribute are 550.000 to 667.500. Instance: %m", MODULE_NAME, CLKPFD_FREQ_MAX_REG);
      attr_err = 1'b1;
    end

    if ((attr_test == 1'b1) ||
        (CLKPFD_FREQ_MIN_REG < 70.000 || CLKPFD_FREQ_MIN_REG > 70.000)) begin
      $display("Error: [Unisim %s-139] CLKPFD_FREQ_MIN attribute is set to %f.  Legal values for this attribute are 70.000 to 70.000. Instance: %m", MODULE_NAME, CLKPFD_FREQ_MIN_REG);
      attr_err = 1'b1;
    end

    if ((attr_test == 1'b1) ||
        ((COMPENSATION_REG != "AUTO") &&
         (COMPENSATION_REG != "BUF_IN") &&
         (COMPENSATION_REG != "INTERNAL") &&
         (COMPENSATION_REG != "PHY_ALIGN"))) begin
      $display("Error: [Unisim %s-140] COMPENSATION attribute is set to %s.  Legal values for this attribute are AUTO, BUF_IN, INTERNAL or PHY_ALIGN. Instance: %m", MODULE_NAME, COMPENSATION_REG);
      attr_err = 1'b1;
    end

    if ((attr_test == 1'b1) ||
         ((DIVCLK_DIVIDE_REG < 1) || (DIVCLK_DIVIDE_REG > 15))) begin
      $display("Error: [Unisim %s-141] DIVCLK_DIVIDE attribute is set to %d.  Legal values for this attribute are 1 to 15. Instance: %m", MODULE_NAME, DIVCLK_DIVIDE_REG);
      attr_err = 1'b1;
    end

    if ((attr_test == 1'b1) ||
        ((IS_CLKFBIN_INVERTED_REG !== 1'b0) && (IS_CLKFBIN_INVERTED_REG !== 1'b1))) begin
      $display("Error: [Unisim %s-142] IS_CLKFBIN_INVERTED attribute is set to %b.  Legal values for this attribute are 1'b0 to 1'b1. Instance: %m", MODULE_NAME, IS_CLKFBIN_INVERTED_REG);
      attr_err = 1'b1;
    end

    if ((attr_test == 1'b1) ||
        ((IS_CLKIN_INVERTED_REG !== 1'b0) && (IS_CLKIN_INVERTED_REG !== 1'b1))) begin
      $display("Error: [Unisim %s-143] IS_CLKIN_INVERTED attribute is set to %b.  Legal values for this attribute are 1'b0 to 1'b1. Instance: %m", MODULE_NAME, IS_CLKIN_INVERTED_REG);
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

    if ((attr_test == 1'b1) ||
        (REF_JITTER_REG < 0.000 || REF_JITTER_REG > 0.999)) begin
      $display("Error: [Unisim %s-150] REF_JITTER attribute is set to %f.  Legal values for this attribute are 0.000 to 0.999. Instance: %m", MODULE_NAME, REF_JITTER_REG);
      attr_err = 1'b1;
    end

    if ((attr_test == 1'b1) ||
        ((STARTUP_WAIT_REG != "TRUE") &&
         (STARTUP_WAIT_REG != "FALSE"))) begin
      $display("Error: [Unisim %s-155] STARTUP_WAIT attribute is set to %s.  Legal values for this attribute are TRUE or FALSE. Instance: %m", MODULE_NAME, STARTUP_WAIT_REG);
      attr_err = 1'b1;
    end

    if ((attr_test == 1'b1) ||
        (VCOCLK_FREQ_MAX_REG < 1200.000 || VCOCLK_FREQ_MAX_REG > 1500.000)) begin
      $display("Error: [Unisim %s-156] VCOCLK_FREQ_MAX attribute is set to %f.  Legal values for this attribute are 1200.000 to 1500.000. Instance: %m", MODULE_NAME, VCOCLK_FREQ_MAX_REG);
      attr_err = 1'b1;
    end

    if ((attr_test == 1'b1) ||
        (VCOCLK_FREQ_MIN_REG < VF_MIN || VCOCLK_FREQ_MIN_REG > VF_MIN)) begin
      $display("Error: [Unisim %s-157] VCOCLK_FREQ_MIN attribute is set to %f.  Legal values for this attribute is %3.3f. Instance: %m", MODULE_NAME, VCOCLK_FREQ_MIN_REG, VF_MIN);
      attr_err = 1'b1;
    end

    if (attr_err == 1'b1) #1 $finish;

    tmp_string = "CLKOUT0_DUTY_CYCLE";
    chk_ok = clkout_duty_chk (CLKOUT0_DIVIDE_REG, CLKOUT0_DUTY_CYCLE_REG, tmp_string);
    tmp_string = "CLKOUT1_DUTY_CYCLE";
    chk_ok = clkout_duty_chk (CLKOUT1_DIVIDE_REG, CLKOUT1_DUTY_CYCLE_REG, tmp_string);


    clkfb_div_fint = CLKFBOUT_MULT_REG;
    clkfbm1_div = CLKFBOUT_MULT_REG;
    clkind_div = DIVCLK_DIVIDE_REG;
    period_vco_max = 1000000 / VCOCLK_FREQ_MIN_REG;
    period_vco_min = 1000000 / VCOCLK_FREQ_MAX_REG;
    period_vco_target = 1000000 / VCOCLK_FREQ_TARGET;
    period_vco_target_half = period_vco_target / 2;
    if (CLKIN_PERIOD_REG < 3.000)
      fb_delay_max = CLKIN_PERIOD_REG;
    else
      fb_delay_max = 3.000;
    pll_lock_time = 12;
    lock_period_time = 10;
    md_product = clkfb_div_fint * DIVCLK_DIVIDE_REG;
    m_product = clkfb_div_fint;
    clkout_en_val = m_product;
    clkout_en_time = md_product + pll_lock_time; 
    locked_en_time = md_product +  clkout_en_time + 2;  
    lock_cnt_max = locked_en_time + 16;

    clk_out_para_cal (clk0_ht, clk0_lt, clk0_nocnt, clk0_edge, CLKOUT0_DIVIDE_REG, CLKOUT0_DUTY_CYCLE_REG);
    clk_out_para_cal (clk1_ht, clk1_lt, clk1_nocnt, clk1_edge, CLKOUT1_DIVIDE_REG, CLKOUT1_DUTY_CYCLE_REG);
    clk_out_para_cal (clkind_ht, clkind_lt, clkind_nocnt, clkind_edge, DIVCLK_DIVIDE_REG, 0.50);
    clk_out_para_cal (clkfbm1_ht, clkfbm1_lt, clkfbm1_nocnt, clkfbm1_edge, clkfb_div_fint, 0.50);
    tmp_string = "CLKOUT0_PHASE";
    clkout_dly_cal (clkout0_dly, CLKOUT0_DIVIDE_REG, CLKOUT0_PHASE_REG, tmp_string);
    tmp_string = "CLKOUT1_PHASE";
    clkout_dly_cal (clkout1_dly,  CLKOUT1_DIVIDE_REG, CLKOUT1_PHASE_REG, tmp_string);
    tmp_string = "CLKFBOUT_PHASE";
    clkout_dly_cal (clkfbm1_dly, clkfb_div_fint, CLKFBOUT_PHASE_REG, tmp_string);

    GetMultVal(clkfb_div_fint,nBandwidth_OPTIMIZED,pll_cp,pll_res,pll_lfhf);

    GetLockDetSettings(clkfb_div_fint,drp_lock_ref_dly,drp_lock_fb_dly,drp_lock_cnt,drp_lock_sat_high,drp_unlock_cnt);

    dr_sram[8] = {3'bx, 1'b1, clk0_ht[5:0], clk0_lt[5:0]};
    dr_sram[9] = {8'b0, clk0_edge, clk0_nocnt, clkout0_dly[5:0]};
    dr_sram[10] = {3'bx, 1'b1, clk1_ht[5:0], clk1_lt[5:0]};
    dr_sram[11] = {1'bx, xiphy_mode[1], xiphy_mode[0],3'bx, 2'b0, clk1_edge, clk1_nocnt, clkout1_dly[5:0]};
    dr_sram[20] = {3'bx, 1'b1, clkfbm1_ht[5:0], clkfbm1_lt[5:0]};
    dr_sram[21] = {8'b0, clkfbm1_edge, clkfbm1_nocnt, clkfbm1_dly[5:0]};
    dr_sram[22] = {2'bx, clkind_edge, clkind_nocnt, clkind_ht[5:0], clkind_lt[5:0]};
    dr_sram[23] = {2'bx, clkfbin_edge, clkfbin_nocnt, clkfbin_ht[5:0], clkfbin_lt[5:0]};
    dr_sram[24] = {6'bx, drp_lock_cnt};
    dr_sram[25] = {1'bx, drp_lock_fb_dly, drp_unlock_cnt};
    dr_sram[26] = {1'bx, drp_lock_ref_dly, drp_lock_sat_high};
    dr_sram[28] = {11'bx, 5'b0};
    dr_sram[78] = {pll_cp[3], 2'bx, pll_cp[2:1], 2'bx, pll_cp[0], 1'b0, 2'bx, pll_cpres, 3'bx};
    dr_sram[79] = {pll_res[3], 2'bx, pll_res[2:1], 2'bx, pll_res[0], pll_lfhf[1], 2'bx, pll_lfhf[0], 4'bx};
  end

  initial
  begin
    clkin_period[0] = 0;
    clkin_period[1] = 0;
    clkin_period[2] = 0;
    clkin_period[3] = 0;
    clkin_period[4] = 0;
    clkin_lost_val = 500;
    clkfb_lost_val = 500;
    period_avg = 0;
    period_fb = 0;
    period_vco = 0;
    period_vco1 = 0;
    period_vco_half = 0;
    period_vco_half1 = 0;
    period_vco_half_rm = 0;
    period_vco_half_rm1 = 0;
    period_vco_half_rm2 = 0;
    period_vco_rm = 0;
    period_vco_cmp_cnt = 0;
    period_vco_cmp_flag = 0;
    clkvco_rm_cnt = 0;
    fb_delay = 0;
    val_tmp = 0;
    dly_tmp = 0;
    fbm1_comp_delay = 0;
    fb_delay_found = 1'b0;
    fb_delay_found_tmp = 1'b0;
    clkin_edge = 0;
    delay_edge = 0;
    clkfb_tst = 1'b0;
    clkout_en = 0;
    clkout_en_t = 0;
    clkout_en0_tmp = 0;
    clkout_en1 = 0;
    pll_locked_tmp1  = 0;
    pll_locked_tmp2  = 0;
    pll_locked_tmp2_dly  = 0;
    pll_locked_tm = 0;
    pll_locked_delay = 0;
    clkout_mux = 3'b0;
    unlock_recover = 0;
    clkin_jit = 0;
    clkin_lock_cnt = 0;
    lock_period = 0;
    drdy_out = 0;
    drdy_out1 = 0;
    locked_out1 = 0;
    locked_out_tmp = 0;
    do_out1 = 16'b0;
    drp_lock = 0;
    drp_lock_lat_cnt = 3'b000;
    clkout0_out = 0;
    clk0_cnt = 9'b0;
    clk1_cnt = 9'b0;
    clkout0_out = 0;
    clkout1_out = 0;
    clk0_out = 0;
    clk1_out = 0;
    clkind_edgei = 0;
    clkind_nocnti = 0;
    clkind_hti = 0;
    clkind_lti = 0;
    clkind_divi = 1;
    clkfbm1_div = 1;
    clkfbm1_div1 = 0;
    clkfbm1_cnt = 8'b0;
    clkind_cnt = 8'b0;
    clkfbm1_nf_out = 0;
    clk0_dly_cnt = 6'b0;
    clk1_dly_cnt = 6'b0;
    clkfbm1_dly_cnt = 6'b0;
    clk0_cnt = 8'b0;
    clk1_cnt = 8'b0;
    clkfbm1_cnt = 8'b0;
    clkfbm2_cnt = 8'b0;
    clkfb_out = 0;
    clkfbm1_nf_out = 0;
    pwron_int = 1;
    #100000 pwron_int = 0;
  end

  assign CLKOUT0 =  clkout0_out;
  assign CLKOUT0B = ~clkout0_out;
  assign CLKOUT1 =  clkout1_out;
  assign CLKOUT1B = ~clkout1_out;
  assign CLKFBOUT = clkfb_out;
//  assign clkoutxiphy_int = xiphy_mode[1] ? (xiphy_mode[0] ? clkind_out : clkvco_by2) : (xiphy_mode[0] ? clkvco : clkvco_2x);
  assign clkoutxiphy_int = xiphy_mode[1] ? clkvco_by2 : (xiphy_mode[0] ? clkvco : clkvco_2x);
  assign CLKOUTPHY = xiphyen_sync & clkoutxiphy_int;

  assign  glock = (startup_wait_sig) ? locked_out_tmp : 1;             // Are these needed
  assign (weak1, strong0) glbl.PLL_LOCKG = (glock == 0) ? 0 : p_up;

initial
begin
    init_chk = 0;
    #2;
    init_chk = 1;
  end
always @(posedge init_chk )
begin
    clkin_chk_t1_r = 1000.000 / CLKIN_FREQ_MIN_REG;
    clkin_chk_t1_i = $rtoi(1000.0 * clkin_chk_t1_r);
    clkin_chk_t1 = 0.001 * clkin_chk_t1_i;
    clkin_chk_t2_r = 1000.000 / CLKIN_FREQ_MAX_REG;
    clkin_chk_t2_i = $rtoi(1000.0 * clkin_chk_t2_r);
    clkin_chk_t2 = 0.001 * clkin_chk_t2_i;

   if (($time > 1) && (CLKIN_PERIOD_REG > clkin_chk_t1 || CLKIN_PERIOD_REG < clkin_chk_t2)) 
   begin
     $display ("Error: [Unisim %s-2] The attribute CLKIN_PERIOD is set to %f ns and out of the allowed range %f ns to %f ns. Instance %m.", MODULE_NAME, CLKIN_PERIOD_REG, clkin_chk_t2, clkin_chk_t1);
     #1 $finish;
   end
   clkvco_freq_init_chk =  (1000.0 * CLKFBOUT_MULT_REG) / (CLKIN_PERIOD_REG * DIVCLK_DIVIDE_REG);

   if (($time > 1) && (clkvco_freq_init_chk > VCOCLK_FREQ_MAX_REG || clkvco_freq_init_chk < VCOCLK_FREQ_MIN_REG)) 
   begin
    $display ("Error: [Unisim %s-3] The calculation of VCO frequency=%f Mhz. This exceeds the permitted VCO frequency range of %f Mhz to %f Mhz. The VCO frequency is calculated with formula: VCO frequency =  CLKFBOUT_MULT / (DIVCLK_DIVIDE * CLKIN_PERIOD). Please adjust the attributes to the permitted VCO frequency range. Instance %m", MODULE_NAME, clkvco_freq_init_chk, VCOCLK_FREQ_MIN_REG, VCOCLK_FREQ_MAX_REG);
    #1 $finish;
   end
   clkpfd_freq_init_chk = (1000.0) / (CLKIN_PERIOD_REG * DIVCLK_DIVIDE_REG);

   if ( ($time > 1)  && (clkpfd_freq_init_chk > CLKPFD_FREQ_MAX_REG || clkpfd_freq_init_chk < CLKPFD_FREQ_MIN_REG)) begin
      $display ("Error: [Unisim %s-4] The calculation of PFD frequency=%f Mhz. This exceeds the permitted PFD frequency range of %f Mhz to %f Mhz. The PFD frequency is calculated with formula: PFD frequency =  1 /(DIVCLK_DIVIDE * CLKIN_PERIOD). Please adjust the attributes to the permitted PFD frequency range. Instance %m", MODULE_NAME, clkpfd_freq_init_chk, CLKPFD_FREQ_MIN_REG, CLKPFD_FREQ_MAX_REG);
      #1 $finish;
   end
  end

  assign pwrdwn_in1 =  (pwrdwn_in === 1) ? 1 : 0;
  assign rst_input  =  (rst_input_r === 1 | pwrdwn_in1 === 1) ? 1 : 0;

  always @(posedge clkin_in or posedge rst_input)
  begin
    if (rst_input)
      rst_in <= 1;
    else
      rst_in <= rst_input ;
  end

  // DRP port read write

  assign do_out = dr_sram[daddr_lat];

  always @(posedge dclk_in or posedge glblGSR)
    if (glblGSR == 1) begin
      drp_lock <= 0;
      drp_lock_lat_cnt <= 3'b000;
      drp_updt <= 1'b0;
    end else begin
      if (~rst_in && drp_updt) drp_updt <= 1'b0;
       if (den_in == 1) begin
        valid_daddr = addr_is_valid(daddr_in);
        if (drp_lock == 1) begin
          $display("Warning: [Unisim %s-14] DEN is high at time %t. Need wait for DRDY signal before next read/write operation through DRP. Instance %m ", MODULE_NAME, $time);
        end else begin
          drp_lock <= 1;
          daddr_lat <= daddr_in;
          drp_lock_lat_cnt <= drp_lock_lat_cnt + 3'b001;
        end
//        if (valid_daddr && ( daddr_in == 7'b1011100 || daddr_in == 7'b1001111 ||
//          daddr_in == 7'b1001110 || (daddr_in >= 7'b0001000 && daddr_in <= 7'b0001011) || 
//	  daddr_in == 7'b0010110 || (daddr_in >= 7'b0011000 && daddr_in <= 7'b0011010))) begin
//        end
//        else begin
        if (valid_daddr == 0) begin
          $display("Warning: [Unisim %s-6] Address DADDR=%b is unsupported at time %t. Instance %m.", MODULE_NAME, DADDR, $time);
        end

        if (dwe_in == 1) begin          // write process
          if (rst_input == 1) begin
//	       if (valid_daddr &&
//              ((daddr_in >= 7'b0001000 && daddr_in <= 7'b0001011) || // 8 - 11
//               (daddr_in >= 7'b0010100 && daddr_in <= 7'b0010110) || // 20 - 22
//               (daddr_in >= 7'b0011000 && daddr_in <= 7'b0011010) || // 24 - 26
//                daddr_in == 7'b1001110 || // 78
//                daddr_in == 7'b1001111 || // 79
//                daddr_in == 7'b1011100)) begin // 92
	          if (valid_daddr) dr_sram[daddr_in] <= di_in;
             if (valid_daddr || drp_updt) drp_updt <= 1'b1;
//             end
             if (daddr_in == 7'b0001000) // 8
               clkout_hl_para_drp (clk0_lt, clk0_ht, di_in, daddr_in);
             if (daddr_in == 7'b0001001) // 9
               clkout_delay_para_drp (clkout0_dly, clk0_nocnt, clk0_edge, di_in, daddr_in);
             if (daddr_in == 7'b0001010) // 10
               clkout_hl_para_drp (clk1_lt, clk1_ht, di_in, daddr_in);
             if (daddr_in == 7'b0001011) // 11
               clkout_delay_para_drp (clkout1_dly, clk1_nocnt, clk1_edge, di_in, daddr_in);
             if (daddr_in == 7'b0010100) begin // 20
               clkout_hl_para_drp (clkfbm1_lt, clkfbm1_ht, di_in, daddr_in);
               clkfbtmp_divi = clkfbm1_ht + clkfbm1_lt;
               if (clkfbtmp_divi > M_MAX || (clkfbtmp_divi < M_MIN))
                  $display("Error: [Unisim %s-7] DI at Address DADDR=%b is %h at at time %t. The sum of DI[11:6] and DI[5:0] is %d and over the range of %d to %d. Instance %m.", MODULE_NAME, daddr_in, di_in, $time, clkfbtmp_divi, M_MIN, M_MAX);
             end
             if (daddr_in == 7'b0010101) begin // 21
               clkout_delay_para_drp (clkfbm1_dly, clkfbm1_nocnt, clkfbm1_edge, di_in, daddr_in);
               clkfbtmp_nocnti = di_in[12];
             end

             if (daddr_in == 7'b0010110) begin // 22
               clkind_lti = {2'b00, di_in[5:0]};
               clkind_hti = {2'b00, di_in[11:6]};
               clkind_lt <= clkind_lti;
               clkind_ht <= clkind_hti;
               clkind_nocnt <= di_in[12];
               clkind_nocnti = di_in[12];
               clkind_edgei = di_in[13];
               clkind_edge <= di_in[13];
               if (di_in[12] == 1)
                      clkind_divi = 8'b00000001;
               else if (di_in[5:0] == 6'b0 && di_in[11:6] == 6'b0)
                      clkind_divi = 8'b10000000;
               else if (di_in[5:0] == 6'b0)
                      clkind_divi = 64 + clkind_hti;
               else if (di_in[11:6] == 6'b0)
                      clkind_divi = 64 + clkind_lti;
               else
                      clkind_divi = clkind_hti + clkind_lti;

               clkind_div <= clkind_divi;
               if (clkind_divi > D_MAX || (clkind_divi < D_MIN && clkind_nocnti == 0))
                  $display("Error: [Unisim %s-8] DI at Address DADDR=%b is %h at time %t. The sum of DI[11:6] and DI[5:0] is %d and over the range of %d to %d. Instance %m.", MODULE_NAME, daddr_in, di_in, $time, clkind_divi, D_MIN, D_MAX);
            end
            if (daddr_in == 7'd24)
              drp_lock_cnt = di_in[9:0];
            if (daddr_in == 7'd25) begin
              drp_lock_fb_dly = di_in[14:10];
              drp_unlock_cnt = di_in[9:0];
            end
            if (daddr_in == 7'd26) begin
              drp_lock_ref_dly = di_in[14:10];
              drp_lock_sat_high = di_in[9:0];
            end
            if (daddr_in == 7'd78) 
              pll_cp = {di_in[15],di_in[12],di_in[11],di_in[8]};
            if (daddr_in == 7'd79)
              pll_res = {di_in[15],di_in[12],di_in[11],di_in[8]};
          end
          else begin
                  $display("Error: [Unisim %s-9] RST is low at time %t. RST needs to be high when changing paramters through DRP. Instance %m ", MODULE_NAME, $time);
          end
        end //DWE
    end  //DEN
    if ( drp_lock == 1) begin
       if (drp_lock_lat_cnt < drp_lock_lat) begin
          drp_lock_lat_cnt <= drp_lock_lat_cnt + 3'b001;
       end
       else begin
          drp_lock <= 0;
          drp_lock_lat_cnt <= 3'b000;
          drdy_out <= 1;
       end
    end
    if (drdy_out == 1) drdy_out <= 0;
  end

  always @ (negedge rst_in) begin
    if (drp_updt) begin
      clkfbtmp_divi = clkfbm1_ht + clkfbm1_lt;
      check_m_settings(clkfbtmp_divi,pll_cp,pll_res,drp_lock_ref_dly,drp_lock_fb_dly,drp_lock_cnt,drp_unlock_cnt,drp_lock_sat_high);
    end
  end

  function addr_is_valid;
  input [6:0] daddr_funcin;
  begin
    addr_is_valid = 1;
    for (i=0; i<=6; i=i+1) begin
      if ( daddr_funcin[i] != 0 && daddr_funcin[i] != 1) addr_is_valid = 0;
    end
    if (addr_is_valid == 1) begin
       if ((daddr_funcin >= 7'b0001000 && daddr_funcin <= 7'b0001011) || // 8 - 11
           (daddr_funcin >= 7'b0010100 && daddr_funcin <= 7'b0010110) || // 20 - 22
           (daddr_funcin >= 7'b0011000 && daddr_funcin <= 7'b0011010) || // 24 - 26
            daddr_funcin == 7'b0011100 || // 28
            daddr_funcin == 7'b1001110 || // 78
            daddr_funcin == 7'b1001111 || // 79
            daddr_funcin == 7'b1011100) begin // 92
            addr_is_valid = 1;
            end
       else begin
            addr_is_valid = 0;
       end
    end
  end
  endfunction


// Determine clock period
 always @(posedge pll_locked_tmp1)
  begin
       pchk_tmp1 = CLKIN_PERIOD_REG * 1100;
       pchk_tmp2 = CLKIN_PERIOD_REG * 900;
       if (period_avg > pchk_tmp1 || period_avg < pchk_tmp2) begin
         $display("Warning: [Unisim %s-10] input CLKIN period (%f) and attribute CLKIN_PERIOD (%f) are not same. Instance %m.", MODULE_NAME, period_avg, CLKIN_PERIOD_REG);
       end
   end

  always @(posedge clkin_in or posedge rst_in)
    if (rst_in)
    begin
      clkin_period[0] <= period_vco_target;
      clkin_period[1] <= period_vco_target;
      clkin_period[2] <= period_vco_target;
      clkin_period[3] <= period_vco_target;
      clkin_period[4] <= period_vco_target;
      clkin_jit <= 0;
      clkin_lock_cnt <= 0;
      pll_locked_tm <= 0;
      lock_period <= 0;
      pll_locked_tmp1 <= 0;
      clkout_en0_tmp <= 0;
      unlock_recover <= 0;
      clkin_edge <= 0;
    end
    else begin
      clkin_edge <= $time;
      if (clkin_edge != 0) begin 
         clkin_period[4] <= clkin_period[3];
         clkin_period[3] <= clkin_period[2];
         clkin_period[2] <= clkin_period[1];
         clkin_period[1] <= clkin_period[0];
         clkin_period[0] <= $time - clkin_edge;
      end
         
      if (pll_unlock == 0 && clkin_edge != 0 && clkinstopped_out == 0)
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
         pll_locked_tm <= 1;
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

  always @(clkin_period[0] or clkin_period[1] or clkin_period[2] or
           clkin_period[3] or clkin_period[4] or period_avg)
  begin
    if (clkin_period[0] > clkin_period[1])
        clkin_period_tmp = clkin_period[0] - clkin_period[1];
    else
        clkin_period_tmp = clkin_period[1] - clkin_period[0];

    if ( (clkin_period[0] != period_avg) && (clkin_period[0] < 1.5 * period_avg || clkin_period_tmp <= 300) ) 
      period_avg = (clkin_period[0] + clkin_period[1] + clkin_period[2] + clkin_period[3] + clkin_period[4])/5;
  end

  always @(period_avg or lock_period or clkind_div)
   if (period_avg > 500 && lock_period == 1)  begin
    clkin_lost_val = ((period_avg * 1.5) / 500) - 1;
    clkfb_lost_val = ((period_avg * 1.5 * clkind_div) / 500) - 1;
  end

    assign  init_trig = 1;
    always @(clk0_ht or clk0_lt or clk0_nocnt or init_trig or clk0_edge)
      clkout_pm_cal(clk0_ht1, clk0_div, clk0_div1, clk0_ht, clk0_lt, clk0_nocnt, clk0_edge);
    always @(clk1_ht or clk1_lt or clk1_nocnt or init_trig  or clk1_edge)
      clkout_pm_cal(clk1_ht1, clk1_div, clk1_div1, clk1_ht, clk1_lt, clk1_nocnt, clk1_edge);
    always @(clkfbm1_ht or clkfbm1_lt or clkfbm1_nocnt or init_trig  or clkfbm1_edge)
      clkout_pm_cal(clkfbm1_ht1, clkfbm1_div, clkfbm1_div1, clkfbm1_ht, clkfbm1_lt, clkfbm1_nocnt, clkfbm1_edge);
    always @(clkind_ht or clkind_lt or clkind_nocnt or init_trig  or clkind_edge)
      clkout_pm_cal(clkind_ht1, clkind_div, clkind_div1, clkind_ht, clkind_lt, clkind_nocnt, clkind_edge);


// Unlock due to jitter

  always @(clkin_jit or rst_in )
  begin
    if (rst_in)
      clkpll_jitter_unlock = 0;
    else
      if (pll_locked_tmp2) begin
        if ((clkin_jit > REF_CLK_JITTER_MAX && clkin_jit < period_avg) ||
            (clkin_jit < -REF_CLK_JITTER_MAX && clkin_jit > -period_avg ))
          clkpll_jitter_unlock = 1;
        else
          clkpll_jitter_unlock = 0;
      end
      else
          clkpll_jitter_unlock = 0;
  end

// Determine feedback delay - only internal feedback

  always @(posedge clkin_in )
    if (fb_delay_found) clkfb_tst <=  1'b0;
    else clkfb_tst <=  ~clkfb_tst;

  always @( posedge clkfb_tst )
      delay_edge = $time;

  assign clkfbin_sel = ((COMPENSATION_BIN == COMPENSATION_INTERNAL) ||
                        ((COMPENSATION_BIN == COMPENSATION_AUTO) && (CLKFBIN === 1'bz)));

  assign CLKFBIN_int = clkfbin_sel && clkfb_out || ~clkfbin_sel && clkfb_in;

  always @( posedge rst_in )
    begin
      fb_delay  <= 0;
      fb_delay_found_tmp <= 1'b0;
    end

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

  always @(negedge clkfb_tst or negedge fb_delay_found_tmp)
       fb_delay_found <= fb_delay_found_tmp;

  always @(fb_delay)
    if (rst_in==0 && (fb_delay/1000.0 > fb_delay_max)) begin
      $display("Warning: [Unisim %s-11] The feedback delay at time %t is %f ns. It is over the maximum value %f ns. Instance %m.", MODULE_NAME, $time, fb_delay / 1000.0, fb_delay_max);
    end


  always @(fb_delay_found_tmp)
    fb_delay_found <= #1000 fb_delay_found_tmp;

  always @(period_avg or clkind_div or clkfbm1_div)
  begin
    if (period_avg > 0 ) 
    begin
      md_product = clkind_div * clkfbm1_div;
      m_product = clkfbm1_div;
      m_product2 = clkfbm1_div / 2;
      period_fb = period_avg * clkind_div;
      period_vco = period_fb / clkfbm1_div;
      period_vco1 = period_vco / 8;
      period_vco2 = period_vco / 4;
      period_vco_mf = period_avg * 8;
      period_vco_rm = period_fb % clkfbm1_div;
      if (period_vco_rm > 1) 
      begin
        if (period_vco_rm > m_product2)  
	begin
          period_vco_cmp_cnt = m_product / (m_product - period_vco_rm) - 1;
          period_vco_cmp_flag = 2;
        end
        else 
        begin
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
    period_vco_half_rm2 = period_vco_half_rm - 1;
    period_vco_half1 = period_vco - period_vco_half + 1;
    pll_locked_delay = period_fb * clkfbm1_div;
    clkin_dly_t =  period_avg * (clkind_div + 1.25);
    clkout_en_val = m_product;
    clkout_en_time = md_product + pll_lock_time; 
    locked_en_time = md_product +  clkout_en_time + 2;  
    lock_cnt_max = locked_en_time + 16;
    end
  end

  always @( clkin_in )    // Why these delays? 
    clkpll_tmp1 <= #(period_avg) clkin_in;

  always @(clkpll_tmp1) 
    clkpll <= #(period_avg) clkpll_tmp1;
  
  always @(clkvco or clkvco_lk_tmp or rst_in) 
  begin
    if (rst_in)
      clkvco  = 0;
    else
      clkvco  = clkvco_lk_tmp;
  end  

// Xiphy clocks

  always @(posedge clkvco or negedge clkvco or posedge rst_in or negedge xiphyen_sync)
  begin
    if (!xiphyen_sync || rst_in)
      clkvco_2x <= 0;
    else 
    begin
      clkvco_2x <= 1;
      #(period_vco/ 4)
      clkvco_2x <= 0;
    end
  end

  always @(posedge clkvco or posedge rst_in) 
  begin
    if (!xiphyen_sync || rst_in)
      clkvco_by2  <= 0;
    else
      clkvco_by2  <= ~clkvco_by2;
  end
 
  always @(posedge clkvco or posedge rst_in) 
  begin
    if (rst_in) begin
      clkvco_by8  <= 1'b0;
      clkvco_cnt <= 2'b0;
    end
    else begin
      if (clkvco_cnt == 2'b0) clkvco_by8  <= ~clkvco_by8;
      clkvco_cnt <= clkvco_cnt + 2'b01;
    end
  end
 
  always @(negedge clkvco_by8 or posedge rst_in) begin
    if (rst_in) begin
      xiphyen_sync2  <= 1'b0;
      xiphyen_sync1  <= 1'b0;
    end
    else begin
      xiphyen_sync2  <= xiphyen_in;
      xiphyen_sync1  <= xiphyen_sync2;
    end
  end

  always @(negedge clkvco or posedge rst_in) begin
    if (rst_in) begin
      xiphyen_sync  <= 1'b0;
    end
    else if (clkvco_cnt[1:0] == 2'b0) begin
      xiphyen_sync  <= xiphyen_sync1;
    end
  end

// VCO clock generation

  always @(posedge clkpll)
  begin
  if (pll_locked_tm ==1) 
  begin
        clkvco_lk_tmp <= 1;
        clkvco_rm_cnt = 0;
        clkout_en_t <= 0;
        vcoflag = 0;
        if ( period_vco_cmp_flag == 1)  
        begin
          for (ik2=1; ik2 < m_product; ik2=ik2+1) 
          begin
          vcoflag = 1;
            clkout_en_t <= ik2;
            #(period_vco_half) clkvco_lk_tmp <= 0;
            if ( clkvco_rm_cnt == 1)
              #(period_vco_half_rm1) clkvco_lk_tmp <= 1;
            else
              #(period_vco_half_rm) clkvco_lk_tmp <= 1;
            if ( clkvco_rm_cnt == period_vco_cmp_cnt) 
              clkvco_rm_cnt <= 0;
            else
              clkvco_rm_cnt <= clkvco_rm_cnt + 1;
          end
          clkout_en_t <= ik2;
        end
        else if ( period_vco_cmp_flag == 2 ) 
        begin
          vcoflag = 1;
          for (ik3=1; ik3 < m_product; ik3=ik3+1) 
	  begin
            clkout_en_t <= ik3;
            #(period_vco_half) clkvco_lk_tmp <= 0;
            if ( clkvco_rm_cnt == 1)
              #(period_vco_half_rm) clkvco_lk_tmp <= 1;
            else
              #(period_vco_half_rm1) clkvco_lk_tmp <= 1;
            if ( clkvco_rm_cnt == period_vco_cmp_cnt)
              clkvco_rm_cnt <= 0;
            else
              clkvco_rm_cnt <= clkvco_rm_cnt + 1;
         end
        clkout_en_t <= ik3;
        end
        else 
	begin
          vcoflag = 1;
          for (ik4=1; ik4 < m_product; ik4=ik4+1) 
          begin
            clkout_en_t <= ik4;
            #(period_vco_half) clkvco_lk_tmp <= 0;
            #(period_vco_half_rm) clkvco_lk_tmp <= 1;
          end
          clkout_en_t <= ik4;
        end
        #(period_vco_half) clkvco_lk_tmp <= 0;
        if (clkpll == 1 && m_product > 1 && m_product != clkind_div && vcoflag == 0) 
	begin
          for (ik4=1; ik4 < m_product; ik4=ik4+1) 
	  begin
            clkout_en_t <= ik4;
            #(period_vco_half) clkvco_lk_tmp <= 0;
            #(period_vco_half_rm) clkvco_lk_tmp <= 1;
          end
          clkout_en_t <= ik4;
          #(period_vco_half) clkvco_lk_tmp <= 0;
        end
    end	
  end  

  always @(fb_delay or period_vco or period_vco_mf or clkfbm1_dly or lock_period) 
  begin	 
    if (lock_period == 1)
    begin
       val_tmp = period_avg * DIVCLK_DIVIDE;
       fbm1_comp_delay = period_vco * clkfbm1_dly;
    end
    dly_tmp1 = fb_delay + fbm1_comp_delay;
    dly_tmp_int = 1;
    dly_tmp = dly_tmp1;
    if (dly_tmp == 0)
      clkvco_delay = 0;
    else if ( dly_tmp < val_tmp)
      clkvco_delay = val_tmp - dly_tmp;
    else
      clkvco_delay = val_tmp - dly_tmp % val_tmp ;
  end
  
  always @(clkvco) 
  begin
    if (clkout_en) 
    begin
      clkout_mux[0] = clkvco;
      clkout_mux[1] <= clkvco;
      clkout_mux[2] <= clkvco;
    end
  end  

  assign clk0in = clkout_mux[0];
  assign clk1in = clkout_mux[1];
  assign clkfbm1in = clkout_mux[2];

  assign clk0ps_en = (clk0_dly_cnt == clkout0_dly) ? clkout_en : 0;
  assign clk1ps_en = (clk1_dly_cnt == clkout1_dly) ? clkout_en : 0;
  assign clkfbm1ps_en = (clkfbm1_dly_cnt == clkfbm1_dly) ? clkout_en : 0;

  always  @(negedge clk0in or posedge rst_in)
  begin
    if (rst_in) 
      clk0_dly_cnt <= 6'b0;
    else
      if (clk0_dly_cnt < clkout0_dly && clkout_en == 1)
        clk0_dly_cnt <= clk0_dly_cnt + 1;
  end  

  always  @(negedge clk1in or posedge rst_in)
  begin 
    if (rst_in)
      clk1_dly_cnt <= 6'b0;
    else
      if (clk1_dly_cnt < clkout1_dly && clkout_en ==1)
        clk1_dly_cnt <= clk1_dly_cnt + 1;
  end
  
  always  @(negedge clkfbm1in or posedge rst_in)
  begin
    if (rst_in) 
        clkfbm1_dly_cnt <= 6'b0;
    else
       if (clkfbm1_dly_cnt < clkfbm1_dly && clkout_en == 1)
          clkfbm1_dly_cnt <= clkfbm1_dly_cnt + 1;
  end

  always @(clk0_out or clkfb_tst or fb_delay_found or rst_in)
  begin
    if (fb_delay_found == 1)
      clkout0_out =  clk0_out;
    else
      if(rst_in == 1'b0)
      clkout0_out = clkfb_tst;
  end
  
  always @(clk1_out or clkfb_tst or fb_delay_found or rst_in)
  begin
    if (fb_delay_found == 1)
      clkout1_out =  clk1_out;
    else
      if(rst_in == 1'b0)
      clkout1_out = clkfb_tst;
  end    

  always @(clkfbm1_out or clkfb_tst or fb_delay_found or rst_in)
  begin
    if (fb_delay_found == 1)
      clkfb_out =  clkfbm1_out;
    else
      if(rst_in == 1'b0)
      clkfb_out = clkfb_tst;
  end    

// Generate unlock signal
  always begin
  if (rst_in)
    clk_osc = 0;
  else
    clk_osc = ~clk_osc;
    #OSC_P2;
  end

  always @(posedge clkpll or negedge clkpll) begin
      clkin_p <= 1;
      clkin_p <= #100 0;
  end

  always @(posedge CLKFBIN_int or negedge CLKFBIN_int) begin
      clkfb_p <= 1;
      clkfb_p <= #100 0;
  end


  always @(posedge clk_osc or posedge rst_in or posedge clkin_p)
  begin
      if (rst_in == 1) begin
        clkinstopped_out <= 0;
        clkin_lost_cnt <= 0;
      end
      else if (clkin_p == 1) begin
        if (clkinstopped_out == 1) begin
          @(posedge clkpll) begin
          clkinstopped_out <= 0;
          clkin_lost_cnt <= 0;
          end
        end
        else begin
           clkinstopped_out <= 0;
           clkin_lost_cnt <= 0;
        end
      end
      else if (lock_period) begin
        if (clkin_lost_cnt < clkin_lost_val) begin
           clkin_lost_cnt <= clkin_lost_cnt + 1;
           clkinstopped_out <= 0;
        end
        else
           clkinstopped_out <= 1;
      end
  end    

  always @(posedge clkinstopped_out or posedge rst_in)
  begin
    if (rst_in);
    else begin
        $display("Warning: [Unisim %s-12] Input CLKIN is stopped at time %t. Reset is required when input clock returns. Instance %m.", MODULE_NAME, $time);
    end
  end  

  always @(posedge clk_osc or posedge rst_in or posedge clkfb_p)
  begin
      if (rst_in == 1 || clkfb_p == 1) begin
        clkfbstopped_out <= 0;
        clkfb_lost_cnt <= 0;
      end
      else if (clkout_en) begin
        if (clkfb_lost_cnt < clkfb_lost_val) begin
           clkfb_lost_cnt <= clkfb_lost_cnt + 1;
           clkfbstopped_out <= 0;
        end
        else
           clkfbstopped_out <= 1;
      end
  end     

  always @(clkin_jit or rst_in )
    begin
    if (rst_in)
       clkpll_jitter_unlock = 0;
    else
   begin
     if (pll_locked_tmp2) 
     begin
        if ((clkin_jit > REF_CLK_JITTER_MAX && clkin_jit < period_avg) ||
             (clkin_jit < -REF_CLK_JITTER_MAX && clkin_jit > -period_avg ))
          clkpll_jitter_unlock = 1;
        else
          clkpll_jitter_unlock = 0;
      end
      else
          clkpll_jitter_unlock = 0;
    end   
  end     

  assign pll_unlock1 = (clkfbstopped_out==1 || clkpll_jitter_unlock == 1) ? 1 : 0; 
  assign pll_unlock = ( clkfbstopped_out==1 || clkpll_jitter_unlock == 1 || unlock_recover == 1) ? 1 : 0;

 // Generate lock signal
  always @(clkout_en0_tmp)
    clkout_en0_tmp1 <= #1 clkout_en0_tmp;

  always @(clkout_en0_tmp1 or clkout_en_t or clkout_en0_tmp )
  begin
    if (clkout_en0_tmp==0 )
      clkout_en0 <= 0;
    else 
    begin
      if (clkout_en_t == clkout_en_val && clkout_en0_tmp1 == 1)
          clkout_en0 <= #(period_vco-1) clkout_en0_tmp1;
    end 
  end

  always @(clkout_en0 )
    clkout_en1 <= #(clkvco_delay) clkout_en0;

  always @(clkout_en1 or rst_in )
  if (rst_in)
    clkout_en <= 0;
  else
    clkout_en <=  clkout_en1;

 always @(pll_locked_tmp1 )
    if (pll_locked_tmp1==0)
      pll_locked_tmp2 <=  pll_locked_tmp1;
    else begin
      pll_locked_tmp2 <= #pll_locked_delay  pll_locked_tmp1;
    end

  always @(rst_in)
    if (rst_in) begin
      assign pll_locked_tmp2 = 0;
      assign clkout_en0 = 0;
    end
    else begin
      deassign pll_locked_tmp2;
      deassign clkout_en0;
    end
    
  assign locked_out = (pll_locked_tm && pll_locked_tmp2_dly && ~pll_unlock && !unlock_recover) ? 1 : 0;
  
  always @(rst_in or locked_out)
     if (rst_in == 1) 
           locked_out_tmp <= #1000 0;
     else
        locked_out_tmp <= locked_out;

// end of lock	

  always @(posedge clk0in or negedge clk0in or posedge rst_in)
  begin
    if (rst_in)
    begin
        clk0_cnt <= 9'b0;
        clk0_out <= 0;
    end
    else if (clk0ps_en)
    begin
      begin
      if (clk0_cnt < clk0_div1)
         clk0_cnt <= clk0_cnt + 1;
      else
         clk0_cnt <= 9'b0;
      if (clk0_cnt < clk0_ht1)
         clk0_out <= 1;
      else
         clk0_out <= 0;
      end
    end
  end

  always @(posedge clk1in or negedge clk1in or posedge rst_in)
  begin
    if (rst_in)
    begin
        clk1_cnt <= 9'b0;
        clk1_out <= 0;
    end
    else if (clk1ps_en)
    begin
          if (clk1_cnt < clk1_div1)
                clk1_cnt <= clk1_cnt + 1;
          else
                clk1_cnt <= 9'b0;
          if (clk1_cnt < clk1_ht1)
                clk1_out <= 1;
          else
                clk1_out <= 0;
      end
    end

  always @(posedge clkpll or negedge clkpll or posedge rst_in)
  begin
    if (rst_in) begin
        clkind_cnt <= 8'b0;
        clkind_out <= 0;
    end
    else if (clkout_en) 
    begin
      if (clkind_cnt < clkind_div1)
        clkind_cnt <= clkind_cnt + 1;
      else
        clkind_cnt <= 8'b0;
      if (clkind_cnt < clkind_ht1)
        clkind_out <= 1;
      else
        clkind_out <= 0;
    end
    else begin
      clkind_cnt <= 8'b0;
      clkind_out <= 0;
    end
  end

  always @(posedge clkfbm1in or negedge clkfbm1in or posedge rst_in)
  begin
    if (rst_in) begin
        clkfbm1_cnt <= 8'b0;
        clkfbm1_nf_out <= 0;
    end
    else if (clkfbm1ps_en) 
    begin
      if (clkfbm1_cnt < clkfbm1_div1)
        clkfbm1_cnt <= clkfbm1_cnt + 1;
      else
        clkfbm1_cnt <= 8'b0;
        if (clkfbm1_cnt < clkfbm1_ht1)
          clkfbm1_nf_out <= 1;
        else
          clkfbm1_nf_out <= 0;
    end
    else 
    begin
        clkfbm1_cnt <= 8'b0;
        clkfbm1_nf_out <= 0;
    end
  end

  assign clkfbm1_out = clkfbm1_nf_out;

  always @(posedge CLKFBIN_int or negedge CLKFBIN_int or posedge rst_in)
  begin
    if (rst_in) begin
        clkfbm2_cnt <= 8'b0;
        clkfbm2_out <= 0;
    end
    else if (clkout_en)  begin
          if (clkfbm2_cnt < clkfbm2_div1)
                clkfbm2_cnt <= clkfbm2_cnt + 1;
          else
                clkfbm2_cnt <= 8'b0;
          if (clkfbm2_cnt < clkfbm2_ht1)
                clkfbm2_out <= 1;
          else
                clkfbm2_out <= 0;
    end
    else begin
        clkfbm2_cnt <= 8'b0;
        clkfbm2_out <= 0;
    end  
 end

// Phase task
  task clkout_dly_cal;
  output [5:0] clkout_dly;
  input  clkdiv;
  input  clk_ps;
  input reg [160:0] clk_ps_name;
  integer clkdiv;
  real clk_ps;
  real clk_ps_rl;
  real clk_dly_rl, clk_dly_rem;
  integer clkout_dly_tmp;
  begin
    if (clk_ps < 0.0)
      clk_dly_rl = (360.0 + clk_ps) * clkdiv / 360.0;
    else
      clk_dly_rl = clk_ps * clkdiv / 360.0;

//    clkout_dly_tmp =  $rtoi(clk_dly_rl);
    clkout_dly_tmp =  clk_dly_rl;

    if (clkout_dly_tmp > 63) begin
      $display("Warning: [Unisim %s-13] Attribute %s is set to %f. Required phase shifting can not be reached since it is over the maximum phase shifting capability. Instance %m ", MODULE_NAME, clk_ps_name, clk_ps);
      clkout_dly = 6'b111111;
    end
    else
      clkout_dly = clkout_dly_tmp;
  end

  endtask

// Task to calculate final ht based on clk_edge 
  task clkout_pm_cal;
  output [8:0] clk_ht1;
  output [8:0] clk_div;
  output [8:0] clk_div1;
  input [7:0] clk_ht;
  input [7:0] clk_lt;
  input clk_nocnt;
  input clk_edge;
  begin
    if (clk_nocnt ==1) begin
        clk_div = 9'b000000001;
        clk_div1 = 9'b000000001;
        clk_ht1 = 9'b000000001;
    end
    else begin
      if ( clk_edge == 1)
        clk_ht1 = 2 * clk_ht + 1;
      else
        clk_ht1 = 2 * clk_ht;
      clk_div = clk_ht  + clk_lt ;
      clk_div1 = 2 * clk_div -1;
    end
  end
  endtask

 // Task to calculate ht, lt based on duty cycle
 // also detects of clk_edge needs to be 1
  task   clk_out_para_cal;
  output [7:0] clk_ht;
  output [7:0] clk_lt;
  output clk_nocnt;
  output clk_edge;
  input  CLKOUT_DIVIDE;
  input  CLKOUT_DUTY_CYCLE;
  integer CLKOUT_DIVIDE;
  real  CLKOUT_DUTY_CYCLE;
  real  tmp_value, tmp_value0, tmp_value_rm;
  integer tmp_value_round, tmp_value1, tmp_value_r;
  real tmp_value2;
  real tmp_value_rm1, tmp_value_r1;
  integer tmp_value_r2;
  begin

     tmp_value0 = CLKOUT_DIVIDE * CLKOUT_DUTY_CYCLE;
     tmp_value_r = $rtoi(tmp_value0);
     tmp_value_rm = tmp_value0 - tmp_value_r;
     if (tmp_value_rm < 0.1)
       tmp_value = tmp_value_r * 1.0;
     else if (tmp_value_rm > 0.9)
       tmp_value = 1.0 * tmp_value_r + 1.0;
     else begin
       tmp_value_r1 = tmp_value0 * 2.0;
       tmp_value_r2 = $rtoi(tmp_value_r1);
       tmp_value_rm1 = tmp_value_r1 - tmp_value_r2;
       if (tmp_value_rm1 > 0.995)
          tmp_value = tmp_value0 + 0.002;
       else
          tmp_value = tmp_value0;
     end
     tmp_value_round = tmp_value * 2.0;
     tmp_value1 =  tmp_value_round % 2;
     tmp_value2 = CLKOUT_DIVIDE - tmp_value;


     if ((tmp_value2) >= O_MAX_HT_LT) begin
       clk_lt = 8'b10000000;
     end
     else begin
       if  (tmp_value2 < 1.0)
          clk_lt = 1;
       else
          if ( tmp_value1  != 0)
             clk_lt = $rtoi(tmp_value2) + 1;
          else
             clk_lt = $rtoi(tmp_value2);
     end

     if ( (CLKOUT_DIVIDE -  clk_lt) >= O_MAX_HT_LT)
       clk_ht = 8'b10000000;
     else
       clk_ht =  CLKOUT_DIVIDE -  clk_lt;

     clk_nocnt = (CLKOUT_DIVIDE ==1) ? 1 : 0;
     if ( tmp_value < 1.0)
       clk_edge = 1;
     else if (tmp_value1 != 0)
       clk_edge = 1;
     else
       clk_edge = 0;
  end
  endtask

  function  clkout_duty_chk;
  input  CLKOUT_DIVIDE;
  input  CLKOUT_DUTY_CYCLE;
  input reg [160:0] CLKOUT_DUTY_CYCLE_N;
  integer CLKOUT_DIVIDE, step_tmp;
  real CLKOUT_DUTY_CYCLE;
  real CLK_DUTY_CYCLE_MIN, CLK_DUTY_CYCLE_MAX, CLK_DUTY_CYCLE_STEP;
  real CLK_DUTY_CYCLE_MIN_rnd;
  reg clk_duty_tmp_int;
  begin
    if (CLKOUT_DIVIDE > O_MAX_HT_LT) begin
      CLK_DUTY_CYCLE_MIN = 1.0 * (CLKOUT_DIVIDE - O_MAX_HT_LT)/CLKOUT_DIVIDE;
      CLK_DUTY_CYCLE_MAX = (O_MAX_HT_LT + 0.5)/CLKOUT_DIVIDE;
      CLK_DUTY_CYCLE_MIN_rnd = CLK_DUTY_CYCLE_MIN;
    end
    else begin
      if (CLKOUT_DIVIDE == 1) begin
        CLK_DUTY_CYCLE_MIN = 0.5;
        CLK_DUTY_CYCLE_MIN_rnd = 0.5;
        CLK_DUTY_CYCLE_MAX = 0.5;
      end
      else begin
        step_tmp = 1000 / CLKOUT_DIVIDE;
        CLK_DUTY_CYCLE_MIN_rnd = step_tmp / 1000.0;
        CLK_DUTY_CYCLE_MIN = 1.0 /CLKOUT_DIVIDE;
        CLK_DUTY_CYCLE_MAX = (CLKOUT_DIVIDE - 0.5)/ CLKOUT_DIVIDE;
      end
    end

    if (CLKOUT_DUTY_CYCLE > CLK_DUTY_CYCLE_MAX || CLKOUT_DUTY_CYCLE < CLK_DUTY_CYCLE_MIN_rnd) begin
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
  reg [1:0] lfhf_unused;
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
  GetMultVal(clkfbout_div,nBandwidth_LOW,pll_cp_low,pll_res_low,lfhf_unused);
  GetMultVal(clkfbout_div,nBandwidth_HIGH,pll_cp_high,pll_res_high,lfhf_unused);
  GetMultVal(clkfbout_div,nBandwidth_OPTIMIZED,pll_cp_optimized,pll_res_optimized,lfhf_unused);
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
      2: begin
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
      default: begin
           lock_ref_dly = 5'd31;
           lock_fb_dly = 5'd31;
           lock_cnt = 10'd250;
         end
   endcase
 end
endtask

task GetMultVal (input integer fClkFbOutMultF, input integer nBandwidth, output [3:0] cp, output [3:0] res, output [1:0] lfhf);
 begin
   if ((nBandwidth == nBandwidth_HIGH) || (nBandwidth == nBandwidth_OPTIMIZED) || (nBandwidth == nBandwidth_LOW))
      lfhf = 2'd3;
      case (fClkFbOutMultF)
         2: begin
              cp = 4'd3; res = 4'd7;
            end
         3: begin
              cp = 4'd3; res = 4'd3;
            end
         4: begin
              cp = 4'd3; res = 4'd9;
            end
         5: begin
              cp = 4'd3; res = 4'd1;
            end
         6: begin
              cp = 4'd4; res = 4'd14;
            end
         7: begin
              cp = 4'd3; res = 4'd6;
            end
         8: begin
              cp = 4'd3; res = 4'd10;
            end
         9,10: begin
              cp = 4'd7; res = 4'd9;
            end
         11: begin
              cp = 4'd5; res = 4'd6;
            end
         12: begin
              cp = 4'd12; res = 4'd5;
            end
         13: begin
              cp = 4'd5; res = 4'd10;
            end
         14: begin
              cp = 4'd6; res = 4'd6;
            end
         15: begin
              cp = 4'd6; res = 4'd10;
            end
         16: begin
              cp = 4'd7; res = 4'd6;
            end
         17: begin
              cp = 4'd15; res = 4'd5;
            end
         18: begin
              cp = 4'd12; res = 4'd6;
            end
         19: begin
              cp = 4'd14; res = 4'd1;
            end
         20: begin
              cp = 4'd13; res = 4'd6;
            end
         21: begin
              cp = 4'd15; res = 4'd1;
            end
      endcase
 end
endtask

  task clkout_delay_para_drp;
  output [5:0] clkout_dly;
  output clk_nocnt;
  output clk_edge;
  input [15:0]  di_in;
  input [6:0] daddr_in;
  begin
     clkout_dly = di_in[5:0];
     clk_nocnt = di_in[6];
     clk_edge = di_in[7];
  end
  endtask

  task clkout_hl_para_drp;
  output  [6:0] clk_lt;
  output  [6:0] clk_ht;
  input [15:0] di_in_tmp;
  input [6:0] daddr_in_tmp;
  begin
//    if (di_in_tmp[12] != 1) begin
//      $display("Error: [Unisim %s-34] Input DI is %h at address DADDR=%b at time %t. The bit 12 needs to be set to 1. Instance %m ", MODULE_NAME, di_in_tmp, daddr_in_tmp, $time);
//    end
    if ( di_in_tmp[5:0] == 6'b0)
       clk_lt = 7'b1000000;
    else
       clk_lt = { 1'b0, di_in_tmp[5:0]};
    if (di_in_tmp[11:6] == 6'b0)
       clk_ht = 7'b1000000;
    else
       clk_ht = { 1'b0, di_in_tmp[11:6]};
  end
  endtask


// end behavioral model

  specify
    (DCLK *> DO) = (100:100:100, 100:100:100);
    (DCLK => DRDY) = (100:100:100, 100:100:100);
    (negedge PWRDWN => (LOCKED +: 0)) = (100:100:100, 100:100:100);
    (negedge RST => (LOCKED +: 0)) = (100:100:100, 100:100:100);
    (posedge PWRDWN => (LOCKED +: 0)) = (100:100:100, 100:100:100);
    (posedge RST => (LOCKED +: 0)) = (100:100:100, 100:100:100);
`ifdef XIL_TIMING
    $period (negedge CLKFBIN, 0:0:0, notifier);
    $period (negedge CLKFBOUT, 0:0:0, notifier);
    $period (negedge CLKIN, 0:0:0, notifier);
    $period (negedge CLKOUT0, 0:0:0, notifier);
    $period (negedge CLKOUT0B, 0:0:0, notifier);
    $period (negedge CLKOUT1, 0:0:0, notifier);
    $period (negedge CLKOUT1B, 0:0:0, notifier);
    $period (negedge CLKOUTPHY, 0:0:0, notifier);
    $period (negedge DCLK, 0:0:0, notifier);
    $period (posedge CLKFBIN, 0:0:0, notifier);
    $period (posedge CLKFBOUT, 0:0:0, notifier);
    $period (posedge CLKIN, 0:0:0, notifier);
    $period (posedge CLKOUT0, 0:0:0, notifier);
    $period (posedge CLKOUT0B, 0:0:0, notifier);
    $period (posedge CLKOUT1, 0:0:0, notifier);
    $period (posedge CLKOUT1B, 0:0:0, notifier);
    $period (posedge CLKOUTPHY, 0:0:0, notifier);
    $period (posedge DCLK, 0:0:0, notifier);
    $setuphold (posedge DCLK, negedge DADDR, 0:0:0, 0:0:0, notifier,,, DCLK_delay, DADDR_delay);
    $setuphold (posedge DCLK, negedge DEN, 0:0:0, 0:0:0, notifier,,, DCLK_delay, DEN_delay);
    $setuphold (posedge DCLK, negedge DI, 0:0:0, 0:0:0, notifier,,, DCLK_delay, DI_delay);
    $setuphold (posedge DCLK, negedge DWE, 0:0:0, 0:0:0, notifier,,, DCLK_delay, DWE_delay);
    $setuphold (posedge DCLK, posedge DADDR, 0:0:0, 0:0:0, notifier,,, DCLK_delay, DADDR_delay);
    $setuphold (posedge DCLK, posedge DEN, 0:0:0, 0:0:0, notifier,,, DCLK_delay, DEN_delay);
    $setuphold (posedge DCLK, posedge DI, 0:0:0, 0:0:0, notifier,,, DCLK_delay, DI_delay);
    $setuphold (posedge DCLK, posedge DWE, 0:0:0, 0:0:0, notifier,,, DCLK_delay, DWE_delay);
    $width (negedge CLKIN, 0:0:0, 0, notifier);
    $width (negedge DCLK, 0:0:0, 0, notifier);
    $width (negedge PWRDWN, 0:0:0, 0, notifier);
    $width (negedge RST, 0:0:0, 0, notifier);
    $width (posedge CLKIN, 0:0:0, 0, notifier);
    $width (posedge DCLK, 0:0:0, 0, notifier);
    $width (posedge PWRDWN, 0:0:0, 0, notifier);
    $width (posedge RST, 0:0:0, 0, notifier);
`endif
    specparam PATHPULSE$ = 0;
  endspecify
endmodule

`endcelldefine
