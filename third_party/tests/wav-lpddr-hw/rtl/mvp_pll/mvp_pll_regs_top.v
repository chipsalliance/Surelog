/*********************************************************************************
Copyright (c) 2021 Wavious LLC

Licensed under the Apache License, Version 2.0 (the "License");
you may not use this file except in compliance with the License.
You may obtain a copy of the License at

    http://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software
distributed under the License is distributed on an "AS IS" BASIS,
WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
See the License for the specific language governing permissions and
limitations under the License.

*********************************************************************************/

//===================================================================
//
// Created by sbridges on December/18/2020 at 05:30:28
//
// mvp_pll_regs_top.v
//
//===================================================================



module mvp_pll_regs_top #(
  parameter    ADDR_WIDTH = 8
)(
  //CORE_OVERRIDES
  input  wire         core_reset,
  output wire         swi_core_reset_muxed,
  input  wire [1:0]   core_vco_sel,
  output wire [1:0]   swi_core_vco_sel_muxed,
  input  wire         core_gfcm_sel,
  output wire         swi_core_gfcm_sel_muxed,
  //CORE_SWTICH_VCO
  output wire         wfifo_core_switch_vco,
  output wire         wfifo_winc_core_switch_vco,
  //CORE_SWTICH_VCO_HW
  input  wire         core_switch_vco_hw,
  output wire         swi_core_switch_vco_hw_muxed,
  //CORE_STATUS
  input  wire         core_ready,
  input  wire         core_fastlock_ready,
  input  wire         core_initial_switch_done,
  input  wire         freq_detect_lock,
  input  wire [16:0]  freq_detect_cycles,
  input  wire [3:0]   fsm_state,
  //CORE_STATUS_INT
  input  wire         w1c_in_loss_of_lock,
  output wire         w1c_out_loss_of_lock,
  input  wire         w1c_in_core_locked,
  output wire         w1c_out_core_locked,
  input  wire         w1c_in_initial_switch_done,
  output wire         w1c_out_initial_switch_done,
  input  wire         w1c_in_vco0_fll_locked,
  output wire         w1c_out_vco0_fll_locked,
  input  wire         w1c_in_vco0_fll_threshold,
  output wire         w1c_out_vco0_fll_threshold,
  input  wire         w1c_in_vco1_fll_locked,
  output wire         w1c_out_vco1_fll_locked,
  input  wire         w1c_in_vco1_fll_threshold,
  output wire         w1c_out_vco1_fll_threshold,
  input  wire         w1c_in_vco2_fll_locked,
  output wire         w1c_out_vco2_fll_locked,
  input  wire         w1c_in_vco2_fll_threshold,
  output wire         w1c_out_vco2_fll_threshold,
  //CORE_STATUS_INT_EN
  output wire         swi_loss_of_lock_int_en,
  output wire         swi_core_locked_int_en,
  output wire         swi_initial_switch_done_int_en,
  output wire         swi_vco0_fll_locked_int_en,
  output wire         swi_vco0_fll_threshold_int_en,
  output wire         swi_vco1_fll_locked_int_en,
  output wire         swi_vco1_fll_threshold_int_en,
  output wire         swi_vco2_fll_locked_int_en,
  output wire         swi_vco2_fll_threshold_int_en,
  //VCO0_BAND
  input  wire [5:0]   vco0_band,
  output wire [5:0]   swi_vco0_band_muxed,
  input  wire [5:0]   vco0_fine,
  output wire [5:0]   swi_vco0_fine_muxed,
  //VCO0_CONTROL
  input  wire         vco0_ena,
  output wire         swi_vco0_ena_muxed,
  output wire         swi_vco0_byp_clk_sel,
  //VCO0_FLL_CONTROL1
  output wire         swi_vco0_fll_enable,
  output wire         swi_vco0_fll_manual_mode,
  output wire [5:0]   swi_vco0_band_start,
  output wire [5:0]   swi_vco0_fine_start,
  output wire [3:0]   swi_vco0_delay_count,
  output wire         swi_vco0_use_demeted_check,
  output wire [3:0]   swi_vco0_locked_count_threshold,
  output wire         swi_vco0_fll_bypass_band,
  output wire         swi_vco0_fll_bypass_fine,
  output wire         swi_vco0_fll_persistent_mode,
  input  wire         vco0_too_fast_status,
  input  wire         vco0_too_slow_status,
  input  wire         vco0_locked,
  //VCO0_FLL_CONTROL2
  output wire [7:0]   swi_vco0_fll_refclk_count,
  output wire [15:0]  swi_vco0_fll_vco_count_target,
  output wire [4:0]   swi_vco0_fll_range,
  //VCO0_FLL_CONTROL3
  output wire [5:0]   swi_vco0_fll_band_thresh,
  //VCO0_FLL_BAND_STATUS
  input  wire [5:0]   vco0_band_status,
  input  wire [5:0]   vco0_band_prev_status,
  input  wire [5:0]   vco0_fine_status,
  input  wire [5:0]   vco0_fine_prev_status,
  //VCO0_FLL_COUNT_STATUS
  input  wire [15:0]  vco0_vco_count,
  //VCO0_INT_FRAC_SETTINGS
  output wire [8:0]   swi_vco0_int,
  output wire [15:0]  swi_vco0_frac,
  output wire         swi_vco0_frac_en,
  output wire         swi_vco0_frac_en_auto,
  //VCO0_PROP_GAINS
  output wire [4:0]   swi_vco0_prop_gain,
  //VCO1_BAND
  input  wire [5:0]   vco1_band,
  output wire [5:0]   swi_vco1_band_muxed,
  input  wire [5:0]   vco1_fine,
  output wire [5:0]   swi_vco1_fine_muxed,
  //VCO1_CONTROL
  input  wire         vco1_ena,
  output wire         swi_vco1_ena_muxed,
  output wire         swi_vco1_byp_clk_sel,
  output wire [1:0]   swi_vco1_post_div,
  //VCO1_FLL_CONTROL1
  output wire         swi_vco1_fll_enable,
  output wire         swi_vco1_fll_manual_mode,
  output wire [5:0]   swi_vco1_band_start,
  output wire [5:0]   swi_vco1_fine_start,
  output wire [3:0]   swi_vco1_delay_count,
  output wire         swi_vco1_use_demeted_check,
  output wire [3:0]   swi_vco1_locked_count_threshold,
  output wire         swi_vco1_fll_bypass_band,
  output wire         swi_vco1_fll_bypass_fine,
  output wire         swi_vco1_fll_persistent_mode,
  input  wire         vco1_too_fast_status,
  input  wire         vco1_too_slow_status,
  input  wire         vco1_locked,
  //VCO1_FLL_CONTROL2
  output wire [7:0]   swi_vco1_fll_refclk_count,
  output wire [15:0]  swi_vco1_fll_vco_count_target,
  output wire [4:0]   swi_vco1_fll_range,
  //VCO1_FLL_CONTROL3
  output wire [5:0]   swi_vco1_fll_band_thresh,
  //VCO1_FLL_BAND_STATUS
  input  wire [5:0]   vco1_band_status,
  input  wire [5:0]   vco1_band_prev_status,
  input  wire [5:0]   vco1_fine_status,
  input  wire [5:0]   vco1_fine_prev_status,
  //VCO1_FLL_COUNT_STATUS
  input  wire [15:0]  vco1_vco_count,
  //VCO1_INT_FRAC_SETTINGS
  output wire [8:0]   swi_vco1_int,
  output wire [15:0]  swi_vco1_frac,
  output wire         swi_vco1_frac_en,
  output wire         swi_vco1_frac_en_auto,
  //VCO1_PROP_GAINS
  output wire [4:0]   swi_vco1_prop_gain,
  //VCO1_SSC_CONTROLS
  output wire         swi_vco1_ssc_enable,
  output wire [9:0]   swi_vco1_ssc_stepsize,
  output wire [16:0]  swi_vco1_ssc_amp,
  output wire         swi_vco1_ssc_count_cycles,
  output wire         swi_vco1_ssc_center_spread,
  //VCO2_BAND
  input  wire [5:0]   vco2_band,
  output wire [5:0]   swi_vco2_band_muxed,
  input  wire [5:0]   vco2_fine,
  output wire [5:0]   swi_vco2_fine_muxed,
  //VCO2_CONTROL
  input  wire         vco2_ena,
  output wire         swi_vco2_ena_muxed,
  output wire         swi_vco2_byp_clk_sel,
  output wire [1:0]   swi_vco2_post_div,
  //VCO2_FLL_CONTROL1
  output wire         swi_vco2_fll_enable,
  output wire         swi_vco2_fll_manual_mode,
  output wire [5:0]   swi_vco2_band_start,
  output wire [5:0]   swi_vco2_fine_start,
  output wire [3:0]   swi_vco2_delay_count,
  output wire         swi_vco2_use_demeted_check,
  output wire [3:0]   swi_vco2_locked_count_threshold,
  output wire         swi_vco2_fll_bypass_band,
  output wire         swi_vco2_fll_bypass_fine,
  output wire         swi_vco2_fll_persistent_mode,
  input  wire         vco2_too_fast_status,
  input  wire         vco2_too_slow_status,
  input  wire         vco2_locked,
  //VCO2_FLL_CONTROL2
  output wire [7:0]   swi_vco2_fll_refclk_count,
  output wire [15:0]  swi_vco2_fll_vco_count_target,
  output wire [4:0]   swi_vco2_fll_range,
  //VCO2_FLL_CONTROL3
  output wire [5:0]   swi_vco2_fll_band_thresh,
  //VCO2_FLL_BAND_STATUS
  input  wire [5:0]   vco2_band_status,
  input  wire [5:0]   vco2_band_prev_status,
  input  wire [5:0]   vco2_fine_status,
  input  wire [5:0]   vco2_fine_prev_status,
  //VCO2_FLL_COUNT_STATUS
  input  wire [15:0]  vco2_vco_count,
  //VCO2_INT_FRAC_SETTINGS
  output wire [8:0]   swi_vco2_int,
  output wire [15:0]  swi_vco2_frac,
  output wire         swi_vco2_frac_en,
  output wire         swi_vco2_frac_en_auto,
  //VCO2_PROP_GAINS
  output wire [4:0]   swi_vco2_prop_gain,
  //VCO2_SSC_CONTROLS
  output wire         swi_vco2_ssc_enable,
  output wire [9:0]   swi_vco2_ssc_stepsize,
  output wire [16:0]  swi_vco2_ssc_amp,
  output wire         swi_vco2_ssc_count_cycles,
  output wire         swi_vco2_ssc_center_spread,
  //STATE_MACHINE_CONTROLS
  output wire [7:0]   swi_bias_settle_count,
  output wire [7:0]   swi_pre_locking_count,
  output wire [3:0]   swi_switch_count,
  output wire         swi_disable_lock_det_after_lock,
  output wire [3:0]   swi_fll_initial_settle,
  //STATE_MACHINE_CONTROLS2
  output wire [3:0]   swi_pre_switch_time,
  output wire [3:0]   swi_switch_reset_time,
  output wire [7:0]   swi_switch_1_time,
  output wire [7:0]   swi_switch_2_time,
  //INTR_GAINS
  output wire [4:0]   swi_normal_int_gain,
  //INTR_PROP_FL_GAINS
  output wire [4:0]   swi_fl_int_gain,
  output wire [4:0]   swi_fl_prop_gain,
  //INTR_PROP_GAINS_OVERRIDE
  input  wire [4:0]   int_gain,
  output wire [4:0]   swi_int_gain_muxed,
  input  wire [4:0]   prop_gain,
  output wire [4:0]   swi_prop_gain_muxed,
  //LOCK_DET_SETTINGS
  output wire [15:0]  swi_ld_refclk_cycles,
  output wire [5:0]   swi_ld_range,
  //FASTLOCK_DET_SETTINGS
  output wire [15:0]  swi_fastld_refclk_cycles,
  output wire [5:0]   swi_fastld_range,
  //ANALOG_EN_RESET
  input  wire         pll_en,
  output wire         swi_pll_en_muxed,
  input  wire         pll_reset,
  output wire         swi_pll_reset_muxed,
  input  wire [8:0]   fbdiv_sel,
  output wire [8:0]   swi_fbdiv_sel_muxed,
  input  wire [1:0]   vco_sel,
  output wire [1:0]   swi_vco_sel_muxed,
  //MODE_DTST_MISC
  output wire [3:0]   swi_bias_lvl,
  output wire         swi_cp_int_mode,
  input  wire         en_lock_det,
  output wire         swi_en_lock_det_muxed,
  output wire         swi_div16en,
  output wire         swi_bias_sel,
  //PROP_CTRLS
  output wire [1:0]   swi_prop_c_ctrl,
  output wire [1:0]   swi_prop_r_ctrl,
  //REFCLK_CONTROLS
  output wire [1:0]   swi_pfd_mode,
  output wire         swi_sel_refclk_alt,
  //CLKGATE_DISABLES
  output wire         swi_force_fbclk_gate,
  output wire         swi_force_vco0_clk_gate,
  output wire         swi_force_vco1_clk_gate,
  output wire         swi_force_vco2_clk_gate,
  //DEBUG_BUS_STATUS
  output reg  [31:0]  debug_bus_ctrl_status,

  //DFT Ports (if used)
  input  wire dft_core_scan_mode,
  input  wire dft_iddq_mode,
  input  wire dft_bscan_mode,
  // BSCAN Shift Interface
  input  wire dft_bscan_tck,
  input  wire dft_bscan_trst_n,
  input  wire dft_bscan_capturedr,
  input  wire dft_bscan_shiftdr,
  input  wire dft_bscan_updatedr,
  input  wire dft_bscan_tdi,
  output wire dft_bscan_tdo,     //Assigned to last in chain

    // AHB Interface
  input  wire RegReset,
  input  wire RegClk,
  input  wire                     hsel,
  input  wire                     hwrite,
  input  wire [1:0]               htrans,
  input  wire [2:0]               hsize,    //not really supporting
  input  wire [2:0]               hburst,   //not really supporting
  input  wire [(ADDR_WIDTH-1):0]  haddr,
  input  wire [31:0]              hwdata,
  output wire [31:0]              hrdata,
  output wire [1:0]               hresp,
  output wire                     hready
);
  
  //DFT Tieoffs (if not used)
  wire dft_hiz_mode = 1'b0;

  //AHB Setup/Access 
  wire [(ADDR_WIDTH-1):0] RegAddr_in;
  reg  [(ADDR_WIDTH-1):0] RegAddr;
  wire [31:0] RegWrData_in;
  //reg  [31:0] RegWrData;
  wire [31:0] RegWrData;
  wire RegWrEn_in;
  reg  RegWrEn;
  wire RegRdEn_in;
  reg  RegRdEn;
  
  wire htrans_valid;
  
  assign htrans_valid = (htrans == 2'b11) || (htrans == 2'b10);

  assign RegAddr_in =            hsel && htrans_valid ? haddr : RegAddr; 
  assign RegWrEn_in = hwrite  && hsel && htrans_valid;
  assign RegRdEn_in = ~hwrite && hsel && htrans_valid;

  always @(posedge RegClk or posedge RegReset) begin
    if (RegReset) begin
      RegAddr   <= {(ADDR_WIDTH){1'b0}};
      RegWrEn   <= 1'b0;
      RegRdEn   <= 1'b0;
      //RegWrData <= 32'h00000000;
    end else begin
      RegAddr   <= RegAddr_in;
      RegWrEn   <= RegWrEn_in;
      RegRdEn   <= RegRdEn_in;
      //RegWrData <= hwdata;
    end
  end
  
  assign RegWrData = hwdata;

  //We are always ready to accept data
  assign hready  = 1'b1;
  


  //Regs for Mux Override sel
  reg  reg_core_reset_mux;
  reg  reg_core_vco_sel_mux;
  reg  reg_core_gfcm_sel_mux;
  reg  reg_core_switch_vco_hw_mux;
  reg  reg_vco0_band_mux;
  reg  reg_vco0_fine_mux;
  reg  reg_vco0_ena_mux;
  reg  reg_vco1_band_mux;
  reg  reg_vco1_fine_mux;
  reg  reg_vco1_ena_mux;
  reg  reg_vco2_band_mux;
  reg  reg_vco2_fine_mux;
  reg  reg_vco2_ena_mux;
  reg  reg_int_gain_mux;
  reg  reg_prop_gain_mux;
  reg  reg_pll_en_mux;
  reg  reg_pll_reset_mux;
  reg  reg_fbdiv_sel_mux;
  reg  reg_vco_sel_mux;
  reg  reg_en_lock_det_mux;



  //---------------------------
  // CORE_OVERRIDES
  // core_reset - Main logic reset
  // core_reset_mux - 1 - Use value from register. 0 - Use value from hardware
  // core_vco_sel - Selects which VCO is in PLL mode. Requires core_switch_vco to be written to take new value.
  // core_vco_sel_mux - 1 - Use value from register. 0 - Use value from hardware
  // core_gfcm_sel - Overrides the GFCM that is external. If you aren't sure what that means, don't play with this.
  // core_gfcm_sel_mux - 
  //---------------------------
  wire [31:0] CORE_OVERRIDES_reg_read;
  reg          reg_core_reset;
  reg  [1:0]   reg_core_vco_sel;
  reg          reg_core_gfcm_sel;

  always @(posedge RegClk or posedge RegReset) begin
    if(RegReset) begin
      reg_core_reset                         <= 1'h0;
      reg_core_reset_mux                     <= 1'h0;
      reg_core_vco_sel                       <= 2'h0;
      reg_core_vco_sel_mux                   <= 1'h0;
      reg_core_gfcm_sel                      <= 1'h0;
      reg_core_gfcm_sel_mux                  <= 1'h0;
    end else if(RegAddr == 'h0 && RegWrEn) begin
      reg_core_reset                         <= RegWrData[0];
      reg_core_reset_mux                     <= RegWrData[1];
      reg_core_vco_sel                       <= RegWrData[3:2];
      reg_core_vco_sel_mux                   <= RegWrData[4];
      reg_core_gfcm_sel                      <= RegWrData[5];
      reg_core_gfcm_sel_mux                  <= RegWrData[6];
    end else begin
      reg_core_reset                         <= reg_core_reset;
      reg_core_reset_mux                     <= reg_core_reset_mux;
      reg_core_vco_sel                       <= reg_core_vco_sel;
      reg_core_vco_sel_mux                   <= reg_core_vco_sel_mux;
      reg_core_gfcm_sel                      <= reg_core_gfcm_sel;
      reg_core_gfcm_sel_mux                  <= reg_core_gfcm_sel_mux;
    end
  end

  assign CORE_OVERRIDES_reg_read = {25'h0,
          reg_core_gfcm_sel_mux,
          reg_core_gfcm_sel,
          reg_core_vco_sel_mux,
          reg_core_vco_sel,
          reg_core_reset_mux,
          reg_core_reset};

  //-----------------------

  wire        swi_core_reset_muxed_pre;
  wav_clock_mux u_wav_clock_mux_core_reset (
    .clk0    ( core_reset                         ),              
    .clk1    ( reg_core_reset                     ),              
    .sel     ( reg_core_reset_mux                 ),      
    .clk_out ( swi_core_reset_muxed_pre           )); 

  assign swi_core_reset_muxed = swi_core_reset_muxed_pre;

  //-----------------------
  //-----------------------

  wire [1:0]  swi_core_vco_sel_muxed_pre;
  wav_clock_mux u_wav_clock_mux_core_vco_sel[1:0] (
    .clk0    ( core_vco_sel                       ),              
    .clk1    ( reg_core_vco_sel                   ),              
    .sel     ( reg_core_vco_sel_mux               ),      
    .clk_out ( swi_core_vco_sel_muxed_pre         )); 

  assign swi_core_vco_sel_muxed = swi_core_vco_sel_muxed_pre;

  //-----------------------
  //-----------------------

  wire        swi_core_gfcm_sel_muxed_pre;
  wav_clock_mux u_wav_clock_mux_core_gfcm_sel (
    .clk0    ( core_gfcm_sel                      ),              
    .clk1    ( reg_core_gfcm_sel                  ),              
    .sel     ( reg_core_gfcm_sel_mux              ),      
    .clk_out ( swi_core_gfcm_sel_muxed_pre        )); 

  assign swi_core_gfcm_sel_muxed = swi_core_gfcm_sel_muxed_pre;

  //-----------------------




  //---------------------------
  // CORE_SWTICH_VCO
  // core_switch_vco - Writing a 1 to this will cause the PLL statemachine to switch to the selected VCO.
  //---------------------------
  wire [31:0] CORE_SWTICH_VCO_reg_read;

  assign wfifo_core_switch_vco      = (RegAddr == 'h4 && RegWrEn) ? RegWrData[0] : 'd0;
  assign wfifo_winc_core_switch_vco = (RegAddr == 'h4 && RegWrEn);
  assign CORE_SWTICH_VCO_reg_read = {31'h0,
          1'd0}; //Reserved

  //-----------------------




  //---------------------------
  // CORE_SWTICH_VCO_HW
  // core_switch_vco_hw - HW Override register for core_switch_vco from external HW source. Basically don't use this register value unless someone tells you
  // core_switch_vco_hw_mux - 
  //---------------------------
  wire [31:0] CORE_SWTICH_VCO_HW_reg_read;
  reg          reg_core_switch_vco_hw;

  always @(posedge RegClk or posedge RegReset) begin
    if(RegReset) begin
      reg_core_switch_vco_hw                 <= 1'h0;
      reg_core_switch_vco_hw_mux             <= 1'h0;
    end else if(RegAddr == 'h8 && RegWrEn) begin
      reg_core_switch_vco_hw                 <= RegWrData[0];
      reg_core_switch_vco_hw_mux             <= RegWrData[1];
    end else begin
      reg_core_switch_vco_hw                 <= reg_core_switch_vco_hw;
      reg_core_switch_vco_hw_mux             <= reg_core_switch_vco_hw_mux;
    end
  end

  assign CORE_SWTICH_VCO_HW_reg_read = {30'h0,
          reg_core_switch_vco_hw_mux,
          reg_core_switch_vco_hw};

  //-----------------------

  wire        swi_core_switch_vco_hw_muxed_pre;
  wav_clock_mux u_wav_clock_mux_core_switch_vco_hw (
    .clk0    ( core_switch_vco_hw                 ),              
    .clk1    ( reg_core_switch_vco_hw             ),              
    .sel     ( reg_core_switch_vco_hw_mux         ),      
    .clk_out ( swi_core_switch_vco_hw_muxed_pre     )); 

  assign swi_core_switch_vco_hw_muxed = swi_core_switch_vco_hw_muxed_pre;

  //-----------------------




  //---------------------------
  // CORE_STATUS
  // core_ready - Asserts when the state machine has gone through the entire lock process
  // core_fastlock_ready - Asserts when the state machine has gone through the fast lock process (but not entire lock)
  // core_initial_switch_done - Asserts when the state machine has gone through the VCO swtich and is on the next VCO.
  // freq_detect_lock - Status of the freq detection circuit
  // freq_detect_cycles - Current FB cycles from freq detection circuit
  // fsm_state - FSM State
  //---------------------------
  wire [31:0] CORE_STATUS_reg_read;
  assign CORE_STATUS_reg_read = {7'h0,
          fsm_state,
          freq_detect_cycles,
          freq_detect_lock,
          core_initial_switch_done,
          core_fastlock_ready,
          core_ready};

  //-----------------------
  //-----------------------
  //-----------------------
  //-----------------------
  //-----------------------
  //-----------------------




  //---------------------------
  // CORE_STATUS_INT
  // loss_of_lock - Asserts when the lock detection circuit loses lock after initially seeing lock. 
  // core_locked - Asserts when the main state machine has gone through the PLL enabling routine and lock has been detected. (Informative)
  // initial_switch_done - Asserts when the main state machine has gone through the initial switch transition.
  // vco0_fll_locked - Asserts when the FLL has completed calibrations and is conceptually locked. (Informative)
  // vco0_fll_threshold - Asserts when the FLL hits the threshold value or higher during freq lock.
  // vco1_fll_locked - Asserts when the FLL has completed calibrations and is conceptually locked. (Informative)
  // vco1_fll_threshold - Asserts when the FLL hits the threshold value or higher during freq lock.
  // vco2_fll_locked - Asserts when the FLL has completed calibrations and is conceptually locked. (Informative)
  // vco2_fll_threshold - Asserts when the FLL hits the threshold value or higher during freq lock.
  //---------------------------
  wire [31:0] CORE_STATUS_INT_reg_read;
  reg          reg_w1c_loss_of_lock;
  wire         reg_w1c_in_loss_of_lock_ff2;
  reg          reg_w1c_in_loss_of_lock_ff3;
  reg          reg_w1c_core_locked;
  wire         reg_w1c_in_core_locked_ff2;
  reg          reg_w1c_in_core_locked_ff3;
  reg          reg_w1c_initial_switch_done;
  wire         reg_w1c_in_initial_switch_done_ff2;
  reg          reg_w1c_in_initial_switch_done_ff3;
  reg          reg_w1c_vco0_fll_locked;
  wire         reg_w1c_in_vco0_fll_locked_ff2;
  reg          reg_w1c_in_vco0_fll_locked_ff3;
  reg          reg_w1c_vco0_fll_threshold;
  wire         reg_w1c_in_vco0_fll_threshold_ff2;
  reg          reg_w1c_in_vco0_fll_threshold_ff3;
  reg          reg_w1c_vco1_fll_locked;
  wire         reg_w1c_in_vco1_fll_locked_ff2;
  reg          reg_w1c_in_vco1_fll_locked_ff3;
  reg          reg_w1c_vco1_fll_threshold;
  wire         reg_w1c_in_vco1_fll_threshold_ff2;
  reg          reg_w1c_in_vco1_fll_threshold_ff3;
  reg          reg_w1c_vco2_fll_locked;
  wire         reg_w1c_in_vco2_fll_locked_ff2;
  reg          reg_w1c_in_vco2_fll_locked_ff3;
  reg          reg_w1c_vco2_fll_threshold;
  wire         reg_w1c_in_vco2_fll_threshold_ff2;
  reg          reg_w1c_in_vco2_fll_threshold_ff3;

  // loss_of_lock W1C Logic
  always @(posedge RegClk or posedge RegReset) begin
    if(RegReset) begin
      reg_w1c_loss_of_lock                      <= 1'h0;
      reg_w1c_in_loss_of_lock_ff3               <= 1'h0;
    end else begin
      reg_w1c_loss_of_lock                      <= RegWrData[0] && reg_w1c_loss_of_lock && (RegAddr == 'h10) && RegWrEn ? 1'b0 : (reg_w1c_in_loss_of_lock_ff2 & ~reg_w1c_in_loss_of_lock_ff3 ? 1'b1 : reg_w1c_loss_of_lock);
      reg_w1c_in_loss_of_lock_ff3               <= reg_w1c_in_loss_of_lock_ff2;
    end
  end

  demet_reset u_demet_reset_loss_of_lock (
    .clk     ( RegClk                                     ),              
    .reset   ( RegReset                                   ),              
    .sig_in  ( w1c_in_loss_of_lock                        ),            
    .sig_out ( reg_w1c_in_loss_of_lock_ff2                )); 


  // core_locked W1C Logic
  always @(posedge RegClk or posedge RegReset) begin
    if(RegReset) begin
      reg_w1c_core_locked                       <= 1'h0;
      reg_w1c_in_core_locked_ff3                <= 1'h0;
    end else begin
      reg_w1c_core_locked                       <= RegWrData[1] && reg_w1c_core_locked && (RegAddr == 'h10) && RegWrEn ? 1'b0 : (reg_w1c_in_core_locked_ff2 & ~reg_w1c_in_core_locked_ff3 ? 1'b1 : reg_w1c_core_locked);
      reg_w1c_in_core_locked_ff3                <= reg_w1c_in_core_locked_ff2;
    end
  end

  demet_reset u_demet_reset_core_locked (
    .clk     ( RegClk                                     ),              
    .reset   ( RegReset                                   ),              
    .sig_in  ( w1c_in_core_locked                         ),            
    .sig_out ( reg_w1c_in_core_locked_ff2                 )); 


  // initial_switch_done W1C Logic
  always @(posedge RegClk or posedge RegReset) begin
    if(RegReset) begin
      reg_w1c_initial_switch_done               <= 1'h0;
      reg_w1c_in_initial_switch_done_ff3        <= 1'h0;
    end else begin
      reg_w1c_initial_switch_done               <= RegWrData[2] && reg_w1c_initial_switch_done && (RegAddr == 'h10) && RegWrEn ? 1'b0 : (reg_w1c_in_initial_switch_done_ff2 & ~reg_w1c_in_initial_switch_done_ff3 ? 1'b1 : reg_w1c_initial_switch_done);
      reg_w1c_in_initial_switch_done_ff3        <= reg_w1c_in_initial_switch_done_ff2;
    end
  end

  demet_reset u_demet_reset_initial_switch_done (
    .clk     ( RegClk                                     ),              
    .reset   ( RegReset                                   ),              
    .sig_in  ( w1c_in_initial_switch_done                 ),            
    .sig_out ( reg_w1c_in_initial_switch_done_ff2         )); 


  // vco0_fll_locked W1C Logic
  always @(posedge RegClk or posedge RegReset) begin
    if(RegReset) begin
      reg_w1c_vco0_fll_locked                   <= 1'h0;
      reg_w1c_in_vco0_fll_locked_ff3            <= 1'h0;
    end else begin
      reg_w1c_vco0_fll_locked                   <= RegWrData[3] && reg_w1c_vco0_fll_locked && (RegAddr == 'h10) && RegWrEn ? 1'b0 : (reg_w1c_in_vco0_fll_locked_ff2 & ~reg_w1c_in_vco0_fll_locked_ff3 ? 1'b1 : reg_w1c_vco0_fll_locked);
      reg_w1c_in_vco0_fll_locked_ff3            <= reg_w1c_in_vco0_fll_locked_ff2;
    end
  end

  demet_reset u_demet_reset_vco0_fll_locked (
    .clk     ( RegClk                                     ),              
    .reset   ( RegReset                                   ),              
    .sig_in  ( w1c_in_vco0_fll_locked                     ),            
    .sig_out ( reg_w1c_in_vco0_fll_locked_ff2             )); 


  // vco0_fll_threshold W1C Logic
  always @(posedge RegClk or posedge RegReset) begin
    if(RegReset) begin
      reg_w1c_vco0_fll_threshold                <= 1'h0;
      reg_w1c_in_vco0_fll_threshold_ff3         <= 1'h0;
    end else begin
      reg_w1c_vco0_fll_threshold                <= RegWrData[4] && reg_w1c_vco0_fll_threshold && (RegAddr == 'h10) && RegWrEn ? 1'b0 : (reg_w1c_in_vco0_fll_threshold_ff2 & ~reg_w1c_in_vco0_fll_threshold_ff3 ? 1'b1 : reg_w1c_vco0_fll_threshold);
      reg_w1c_in_vco0_fll_threshold_ff3         <= reg_w1c_in_vco0_fll_threshold_ff2;
    end
  end

  demet_reset u_demet_reset_vco0_fll_threshold (
    .clk     ( RegClk                                     ),              
    .reset   ( RegReset                                   ),              
    .sig_in  ( w1c_in_vco0_fll_threshold                  ),            
    .sig_out ( reg_w1c_in_vco0_fll_threshold_ff2          )); 


  // vco1_fll_locked W1C Logic
  always @(posedge RegClk or posedge RegReset) begin
    if(RegReset) begin
      reg_w1c_vco1_fll_locked                   <= 1'h0;
      reg_w1c_in_vco1_fll_locked_ff3            <= 1'h0;
    end else begin
      reg_w1c_vco1_fll_locked                   <= RegWrData[5] && reg_w1c_vco1_fll_locked && (RegAddr == 'h10) && RegWrEn ? 1'b0 : (reg_w1c_in_vco1_fll_locked_ff2 & ~reg_w1c_in_vco1_fll_locked_ff3 ? 1'b1 : reg_w1c_vco1_fll_locked);
      reg_w1c_in_vco1_fll_locked_ff3            <= reg_w1c_in_vco1_fll_locked_ff2;
    end
  end

  demet_reset u_demet_reset_vco1_fll_locked (
    .clk     ( RegClk                                     ),              
    .reset   ( RegReset                                   ),              
    .sig_in  ( w1c_in_vco1_fll_locked                     ),            
    .sig_out ( reg_w1c_in_vco1_fll_locked_ff2             )); 


  // vco1_fll_threshold W1C Logic
  always @(posedge RegClk or posedge RegReset) begin
    if(RegReset) begin
      reg_w1c_vco1_fll_threshold                <= 1'h0;
      reg_w1c_in_vco1_fll_threshold_ff3         <= 1'h0;
    end else begin
      reg_w1c_vco1_fll_threshold                <= RegWrData[6] && reg_w1c_vco1_fll_threshold && (RegAddr == 'h10) && RegWrEn ? 1'b0 : (reg_w1c_in_vco1_fll_threshold_ff2 & ~reg_w1c_in_vco1_fll_threshold_ff3 ? 1'b1 : reg_w1c_vco1_fll_threshold);
      reg_w1c_in_vco1_fll_threshold_ff3         <= reg_w1c_in_vco1_fll_threshold_ff2;
    end
  end

  demet_reset u_demet_reset_vco1_fll_threshold (
    .clk     ( RegClk                                     ),              
    .reset   ( RegReset                                   ),              
    .sig_in  ( w1c_in_vco1_fll_threshold                  ),            
    .sig_out ( reg_w1c_in_vco1_fll_threshold_ff2          )); 


  // vco2_fll_locked W1C Logic
  always @(posedge RegClk or posedge RegReset) begin
    if(RegReset) begin
      reg_w1c_vco2_fll_locked                   <= 1'h0;
      reg_w1c_in_vco2_fll_locked_ff3            <= 1'h0;
    end else begin
      reg_w1c_vco2_fll_locked                   <= RegWrData[7] && reg_w1c_vco2_fll_locked && (RegAddr == 'h10) && RegWrEn ? 1'b0 : (reg_w1c_in_vco2_fll_locked_ff2 & ~reg_w1c_in_vco2_fll_locked_ff3 ? 1'b1 : reg_w1c_vco2_fll_locked);
      reg_w1c_in_vco2_fll_locked_ff3            <= reg_w1c_in_vco2_fll_locked_ff2;
    end
  end

  demet_reset u_demet_reset_vco2_fll_locked (
    .clk     ( RegClk                                     ),              
    .reset   ( RegReset                                   ),              
    .sig_in  ( w1c_in_vco2_fll_locked                     ),            
    .sig_out ( reg_w1c_in_vco2_fll_locked_ff2             )); 


  // vco2_fll_threshold W1C Logic
  always @(posedge RegClk or posedge RegReset) begin
    if(RegReset) begin
      reg_w1c_vco2_fll_threshold                <= 1'h0;
      reg_w1c_in_vco2_fll_threshold_ff3         <= 1'h0;
    end else begin
      reg_w1c_vco2_fll_threshold                <= RegWrData[8] && reg_w1c_vco2_fll_threshold && (RegAddr == 'h10) && RegWrEn ? 1'b0 : (reg_w1c_in_vco2_fll_threshold_ff2 & ~reg_w1c_in_vco2_fll_threshold_ff3 ? 1'b1 : reg_w1c_vco2_fll_threshold);
      reg_w1c_in_vco2_fll_threshold_ff3         <= reg_w1c_in_vco2_fll_threshold_ff2;
    end
  end

  demet_reset u_demet_reset_vco2_fll_threshold (
    .clk     ( RegClk                                     ),              
    .reset   ( RegReset                                   ),              
    .sig_in  ( w1c_in_vco2_fll_threshold                  ),            
    .sig_out ( reg_w1c_in_vco2_fll_threshold_ff2          )); 

  assign CORE_STATUS_INT_reg_read = {23'h0,
          reg_w1c_vco2_fll_threshold,
          reg_w1c_vco2_fll_locked,
          reg_w1c_vco1_fll_threshold,
          reg_w1c_vco1_fll_locked,
          reg_w1c_vco0_fll_threshold,
          reg_w1c_vco0_fll_locked,
          reg_w1c_initial_switch_done,
          reg_w1c_core_locked,
          reg_w1c_loss_of_lock};

  //-----------------------
  assign w1c_out_loss_of_lock = reg_w1c_loss_of_lock;
  //-----------------------
  assign w1c_out_core_locked = reg_w1c_core_locked;
  //-----------------------
  assign w1c_out_initial_switch_done = reg_w1c_initial_switch_done;
  //-----------------------
  assign w1c_out_vco0_fll_locked = reg_w1c_vco0_fll_locked;
  //-----------------------
  assign w1c_out_vco0_fll_threshold = reg_w1c_vco0_fll_threshold;
  //-----------------------
  assign w1c_out_vco1_fll_locked = reg_w1c_vco1_fll_locked;
  //-----------------------
  assign w1c_out_vco1_fll_threshold = reg_w1c_vco1_fll_threshold;
  //-----------------------
  assign w1c_out_vco2_fll_locked = reg_w1c_vco2_fll_locked;
  //-----------------------
  assign w1c_out_vco2_fll_threshold = reg_w1c_vco2_fll_threshold;




  //---------------------------
  // CORE_STATUS_INT_EN
  // loss_of_lock_int_en - 1 - Enables loss_of_lock interrupt
  // core_locked_int_en - 1 - Enables the core_locked interrupt
  // initial_switch_done_int_en - 1 - Enables the initial_switch_done interrupt
  // vco0_fll_locked_int_en - 1 - Enables the fll_locked interrupt
  // vco0_fll_threshold_int_en - 1 - Enables fll_threshold interrupt
  // vco1_fll_locked_int_en - 1 - Enables the fll_locked interrupt
  // vco1_fll_threshold_int_en - 1 - Enables fll_threshold interrupt
  // vco2_fll_locked_int_en - 1 - Enables the fll_locked interrupt
  // vco2_fll_threshold_int_en - 1 - Enables fll_threshold interrupt
  //---------------------------
  wire [31:0] CORE_STATUS_INT_EN_reg_read;
  reg         reg_loss_of_lock_int_en;
  reg         reg_core_locked_int_en;
  reg         reg_initial_switch_done_int_en;
  reg         reg_vco0_fll_locked_int_en;
  reg         reg_vco0_fll_threshold_int_en;
  reg         reg_vco1_fll_locked_int_en;
  reg         reg_vco1_fll_threshold_int_en;
  reg         reg_vco2_fll_locked_int_en;
  reg         reg_vco2_fll_threshold_int_en;

  always @(posedge RegClk or posedge RegReset) begin
    if(RegReset) begin
      reg_loss_of_lock_int_en                <= 1'h0;
      reg_core_locked_int_en                 <= 1'h0;
      reg_initial_switch_done_int_en         <= 1'h0;
      reg_vco0_fll_locked_int_en             <= 1'h0;
      reg_vco0_fll_threshold_int_en          <= 1'h0;
      reg_vco1_fll_locked_int_en             <= 1'h0;
      reg_vco1_fll_threshold_int_en          <= 1'h0;
      reg_vco2_fll_locked_int_en             <= 1'h0;
      reg_vco2_fll_threshold_int_en          <= 1'h0;
    end else if(RegAddr == 'h14 && RegWrEn) begin
      reg_loss_of_lock_int_en                <= RegWrData[0];
      reg_core_locked_int_en                 <= RegWrData[1];
      reg_initial_switch_done_int_en         <= RegWrData[2];
      reg_vco0_fll_locked_int_en             <= RegWrData[3];
      reg_vco0_fll_threshold_int_en          <= RegWrData[4];
      reg_vco1_fll_locked_int_en             <= RegWrData[5];
      reg_vco1_fll_threshold_int_en          <= RegWrData[6];
      reg_vco2_fll_locked_int_en             <= RegWrData[7];
      reg_vco2_fll_threshold_int_en          <= RegWrData[8];
    end else begin
      reg_loss_of_lock_int_en                <= reg_loss_of_lock_int_en;
      reg_core_locked_int_en                 <= reg_core_locked_int_en;
      reg_initial_switch_done_int_en         <= reg_initial_switch_done_int_en;
      reg_vco0_fll_locked_int_en             <= reg_vco0_fll_locked_int_en;
      reg_vco0_fll_threshold_int_en          <= reg_vco0_fll_threshold_int_en;
      reg_vco1_fll_locked_int_en             <= reg_vco1_fll_locked_int_en;
      reg_vco1_fll_threshold_int_en          <= reg_vco1_fll_threshold_int_en;
      reg_vco2_fll_locked_int_en             <= reg_vco2_fll_locked_int_en;
      reg_vco2_fll_threshold_int_en          <= reg_vco2_fll_threshold_int_en;
    end
  end

  assign CORE_STATUS_INT_EN_reg_read = {23'h0,
          reg_vco2_fll_threshold_int_en,
          reg_vco2_fll_locked_int_en,
          reg_vco1_fll_threshold_int_en,
          reg_vco1_fll_locked_int_en,
          reg_vco0_fll_threshold_int_en,
          reg_vco0_fll_locked_int_en,
          reg_initial_switch_done_int_en,
          reg_core_locked_int_en,
          reg_loss_of_lock_int_en};

  //-----------------------
  assign swi_loss_of_lock_int_en = reg_loss_of_lock_int_en;

  //-----------------------
  assign swi_core_locked_int_en = reg_core_locked_int_en;

  //-----------------------
  assign swi_initial_switch_done_int_en = reg_initial_switch_done_int_en;

  //-----------------------
  assign swi_vco0_fll_locked_int_en = reg_vco0_fll_locked_int_en;

  //-----------------------
  assign swi_vco0_fll_threshold_int_en = reg_vco0_fll_threshold_int_en;

  //-----------------------
  assign swi_vco1_fll_locked_int_en = reg_vco1_fll_locked_int_en;

  //-----------------------
  assign swi_vco1_fll_threshold_int_en = reg_vco1_fll_threshold_int_en;

  //-----------------------
  assign swi_vco2_fll_locked_int_en = reg_vco2_fll_locked_int_en;

  //-----------------------
  assign swi_vco2_fll_threshold_int_en = reg_vco2_fll_threshold_int_en;





  //---------------------------
  // VCO0_BAND
  // vco0_band - Binary representation of VCO band
  // vco0_band_mux - 1 - Use value from register. 0 - Hardware controlled
  // reserved0 - 
  // vco0_fine - VCO Fine Control Value
  // vco0_fine_mux - 1 - Use value from register. 0 - Hardware controlled
  //---------------------------
  wire [31:0] VCO0_BAND_reg_read;
  reg  [5:0]   reg_vco0_band;
  reg  [5:0]   reg_vco0_fine;

  always @(posedge RegClk or posedge RegReset) begin
    if(RegReset) begin
      reg_vco0_band                          <= 6'h0;
      reg_vco0_band_mux                      <= 1'h1;
      reg_vco0_fine                          <= 6'h1f;
      reg_vco0_fine_mux                      <= 1'h1;
    end else if(RegAddr == 'h18 && RegWrEn) begin
      reg_vco0_band                          <= RegWrData[5:0];
      reg_vco0_band_mux                      <= RegWrData[6];
      reg_vco0_fine                          <= RegWrData[13:8];
      reg_vco0_fine_mux                      <= RegWrData[14];
    end else begin
      reg_vco0_band                          <= reg_vco0_band;
      reg_vco0_band_mux                      <= reg_vco0_band_mux;
      reg_vco0_fine                          <= reg_vco0_fine;
      reg_vco0_fine_mux                      <= reg_vco0_fine_mux;
    end
  end

  assign VCO0_BAND_reg_read = {17'h0,
          reg_vco0_fine_mux,
          reg_vco0_fine,
          1'd0, //Reserved
          reg_vco0_band_mux,
          reg_vco0_band};

  //-----------------------

  wire [5:0]  swi_vco0_band_muxed_pre;
  wav_clock_mux u_wav_clock_mux_vco0_band[5:0] (
    .clk0    ( vco0_band                          ),              
    .clk1    ( reg_vco0_band                      ),              
    .sel     ( reg_vco0_band_mux                  ),      
    .clk_out ( swi_vco0_band_muxed_pre            )); 

  wire [5:0] vco0_band_tdo;


  wire [5:0] vco0_band_bscan_flop_po;
  mvp_pll_jtag_bsr u_mvp_pll_jtag_bsr_vco0_band[5:0] (   
    .tck        ( dft_bscan_tck                      ),          
    .trst_n     ( dft_bscan_trst_n                   ),      
    .bscan_mode ( dft_bscan_mode                     ),
    .capturedr  ( dft_bscan_capturedr                ),
    .shiftdr    ( dft_bscan_shiftdr                  ),          
    .updatedr   ( dft_bscan_updatedr                 ),               
    .pi         ( swi_vco0_band_muxed_pre            ),               
    .po         ( vco0_band_bscan_flop_po            ),               
    .tdi        ( {vco0_band_tdo[4],
                   vco0_band_tdo[3],
                   vco0_band_tdo[2],
                   vco0_band_tdo[1],
                   vco0_band_tdo[0],
                   dft_bscan_tdi}     ),                
    .tdo        ( {vco0_band_tdo[5],
                   vco0_band_tdo[4],
                   vco0_band_tdo[3],
                   vco0_band_tdo[2],
                   vco0_band_tdo[1],
                   vco0_band_tdo[0]}     )); 

  assign swi_vco0_band_muxed = vco0_band_bscan_flop_po;

  //-----------------------
  //-----------------------
  //-----------------------

  wire [5:0]  swi_vco0_fine_muxed_pre;
  wav_clock_mux u_wav_clock_mux_vco0_fine[5:0] (
    .clk0    ( vco0_fine                          ),              
    .clk1    ( reg_vco0_fine                      ),              
    .sel     ( reg_vco0_fine_mux                  ),      
    .clk_out ( swi_vco0_fine_muxed_pre            )); 

  wire [5:0] vco0_fine_tdo;


  wire [5:0] vco0_fine_bscan_flop_po;
  mvp_pll_jtag_bsr u_mvp_pll_jtag_bsr_vco0_fine[5:0] (   
    .tck        ( dft_bscan_tck                      ),          
    .trst_n     ( dft_bscan_trst_n                   ),      
    .bscan_mode ( dft_bscan_mode                     ),
    .capturedr  ( dft_bscan_capturedr                ),
    .shiftdr    ( dft_bscan_shiftdr                  ),          
    .updatedr   ( dft_bscan_updatedr                 ),               
    .pi         ( swi_vco0_fine_muxed_pre            ),               
    .po         ( vco0_fine_bscan_flop_po            ),               
    .tdi        ( {vco0_fine_tdo[4],
                   vco0_fine_tdo[3],
                   vco0_fine_tdo[2],
                   vco0_fine_tdo[1],
                   vco0_fine_tdo[0],
                   vco0_band_tdo[5]}     ),                
    .tdo        ( {vco0_fine_tdo[5],
                   vco0_fine_tdo[4],
                   vco0_fine_tdo[3],
                   vco0_fine_tdo[2],
                   vco0_fine_tdo[1],
                   vco0_fine_tdo[0]}     )); 

  assign swi_vco0_fine_muxed = vco0_fine_bscan_flop_po;

  //-----------------------




  //---------------------------
  // VCO0_CONTROL
  // vco0_ena - Main Enable of the VCO
  // vco0_ena_mux - 1 - Use value from vco0_ena. 0 - Hardware controlled
  // vco0_byp_clk_sel - Uses refclk for VCO output clock
  //---------------------------
  wire [31:0] VCO0_CONTROL_reg_read;
  reg          reg_vco0_ena;
  reg         reg_vco0_byp_clk_sel;

  always @(posedge RegClk or posedge RegReset) begin
    if(RegReset) begin
      reg_vco0_ena                           <= 1'h0;
      reg_vco0_ena_mux                       <= 1'h0;
      reg_vco0_byp_clk_sel                   <= 1'h0;
    end else if(RegAddr == 'h1c && RegWrEn) begin
      reg_vco0_ena                           <= RegWrData[0];
      reg_vco0_ena_mux                       <= RegWrData[1];
      reg_vco0_byp_clk_sel                   <= RegWrData[2];
    end else begin
      reg_vco0_ena                           <= reg_vco0_ena;
      reg_vco0_ena_mux                       <= reg_vco0_ena_mux;
      reg_vco0_byp_clk_sel                   <= reg_vco0_byp_clk_sel;
    end
  end

  assign VCO0_CONTROL_reg_read = {29'h0,
          reg_vco0_byp_clk_sel,
          reg_vco0_ena_mux,
          reg_vco0_ena};

  //-----------------------

  wire        swi_vco0_ena_muxed_pre;
  wav_clock_mux u_wav_clock_mux_vco0_ena (
    .clk0    ( vco0_ena                           ),              
    .clk1    ( reg_vco0_ena                       ),              
    .sel     ( reg_vco0_ena_mux                   ),      
    .clk_out ( swi_vco0_ena_muxed_pre             )); 


  wire        reg_vco0_ena_core_scan_mode;
  wav_clock_mux u_wav_clock_mux_vco0_ena_core_scan_mode (
    .clk0    ( swi_vco0_ena_muxed_pre             ),              
    .clk1    ( 1'd0                               ),              
    .sel     ( dft_core_scan_mode                 ),      
    .clk_out ( reg_vco0_ena_core_scan_mode        )); 


  wire        reg_vco0_ena_iddq_mode;
  wav_clock_mux u_wav_clock_mux_vco0_ena_iddq_mode (
    .clk0    ( reg_vco0_ena_core_scan_mode        ),              
    .clk1    ( 1'd0                               ),              
    .sel     ( dft_iddq_mode                      ),      
    .clk_out ( reg_vco0_ena_iddq_mode             )); 

  wire  vco0_ena_tdo;


  wire  vco0_ena_bscan_flop_po;
  mvp_pll_jtag_bsr u_mvp_pll_jtag_bsr_vco0_ena (   
    .tck        ( dft_bscan_tck                      ),          
    .trst_n     ( dft_bscan_trst_n                   ),      
    .bscan_mode ( dft_bscan_mode                     ),
    .capturedr  ( dft_bscan_capturedr                ),
    .shiftdr    ( dft_bscan_shiftdr                  ),          
    .updatedr   ( dft_bscan_updatedr                 ),               
    .pi         ( reg_vco0_ena_iddq_mode             ),               
    .po         ( vco0_ena_bscan_flop_po             ),               
    .tdi        ( vco0_fine_tdo[5]                   ),                
    .tdo        ( vco0_ena_tdo                       )); 

  assign swi_vco0_ena_muxed = vco0_ena_bscan_flop_po;

  //-----------------------
  //-----------------------
  wire  vco0_byp_clk_sel_tdo;


  wire  vco0_byp_clk_sel_bscan_flop_po;
  mvp_pll_jtag_bsr u_mvp_pll_jtag_bsr_vco0_byp_clk_sel (   
    .tck        ( dft_bscan_tck                      ),          
    .trst_n     ( dft_bscan_trst_n                   ),      
    .bscan_mode ( dft_bscan_mode                     ),
    .capturedr  ( dft_bscan_capturedr                ),
    .shiftdr    ( dft_bscan_shiftdr                  ),          
    .updatedr   ( dft_bscan_updatedr                 ),               
    .pi         ( reg_vco0_byp_clk_sel               ),               
    .po         ( vco0_byp_clk_sel_bscan_flop_po     ),               
    .tdi        ( vco0_ena_tdo                       ),                
    .tdo        ( vco0_byp_clk_sel_tdo               )); 

  assign swi_vco0_byp_clk_sel = vco0_byp_clk_sel_bscan_flop_po;





  //---------------------------
  // VCO0_FLL_CONTROL1
  // vco0_fll_enable - Enables FLL
  // vco0_fll_manual_mode - 0 - FLL will continually change band, 1 - FLL will run once (used for manual SW calibration of band)
  // vco0_band_start - Starting band upon enabling FLL. This should match the same band used to lock the VCO0 in PLL mode.
  // vco0_fine_start - Starting fine code upon enabling FLL. This should match the same fine code used to lock the VCO0 in PLL mode.
  // vco0_delay_count - Number of Refclk Cycles to wait after deactivation of counters before checking up/dn
  // vco0_use_demeted_check - 1 - up/dn check is based on demeted signals, 0 - up/dn is coming from VCO clock domain (ensure enough delay thorugh delay count)
  // vco0_locked_count_threshold - Number of consecutive cycles where band toggles +/-1 before indicating locked
  // vco0_fll_bypass_band - 1 - Band code is not calibrated during FLL enable. User would want to set the vco_band_start to the desired band setting
  // vco0_fll_bypass_fine - 1 - Fine code is not calibrated during FLL enable. User would want to set the vco_fine_start to the desired band setting
  // vco0_fll_persistent_mode - 0 - FLL will run until lock is detected and will hold code. 1 - FLL will continue to run, adapting to frequency changes. 
  // vco0_too_fast_status - Asserted if VCO count is higher than target + range (use during manual SW calibration)
  // vco0_too_slow_status - Asserted if VCO count is lower than target + range (use during manual SW calibration)
  // vco0_locked - FLL lock indication 
  //---------------------------
  wire [31:0] VCO0_FLL_CONTROL1_reg_read;
  reg         reg_vco0_fll_enable;
  reg         reg_vco0_fll_manual_mode;
  reg [5:0]   reg_vco0_band_start;
  reg [5:0]   reg_vco0_fine_start;
  reg [3:0]   reg_vco0_delay_count;
  reg         reg_vco0_use_demeted_check;
  reg [3:0]   reg_vco0_locked_count_threshold;
  reg         reg_vco0_fll_bypass_band;
  reg         reg_vco0_fll_bypass_fine;
  reg         reg_vco0_fll_persistent_mode;

  always @(posedge RegClk or posedge RegReset) begin
    if(RegReset) begin
      reg_vco0_fll_enable                    <= 1'h0;
      reg_vco0_fll_manual_mode               <= 1'h0;
      reg_vco0_band_start                    <= 6'h1f;
      reg_vco0_fine_start                    <= 6'h1f;
      reg_vco0_delay_count                   <= 4'h2;
      reg_vco0_use_demeted_check             <= 1'h1;
      reg_vco0_locked_count_threshold        <= 4'h4;
      reg_vco0_fll_bypass_band               <= 1'h1;
      reg_vco0_fll_bypass_fine               <= 1'h0;
      reg_vco0_fll_persistent_mode           <= 1'h1;
    end else if(RegAddr == 'h20 && RegWrEn) begin
      reg_vco0_fll_enable                    <= RegWrData[0];
      reg_vco0_fll_manual_mode               <= RegWrData[1];
      reg_vco0_band_start                    <= RegWrData[7:2];
      reg_vco0_fine_start                    <= RegWrData[13:8];
      reg_vco0_delay_count                   <= RegWrData[17:14];
      reg_vco0_use_demeted_check             <= RegWrData[18];
      reg_vco0_locked_count_threshold        <= RegWrData[22:19];
      reg_vco0_fll_bypass_band               <= RegWrData[23];
      reg_vco0_fll_bypass_fine               <= RegWrData[24];
      reg_vco0_fll_persistent_mode           <= RegWrData[25];
    end else begin
      reg_vco0_fll_enable                    <= reg_vco0_fll_enable;
      reg_vco0_fll_manual_mode               <= reg_vco0_fll_manual_mode;
      reg_vco0_band_start                    <= reg_vco0_band_start;
      reg_vco0_fine_start                    <= reg_vco0_fine_start;
      reg_vco0_delay_count                   <= reg_vco0_delay_count;
      reg_vco0_use_demeted_check             <= reg_vco0_use_demeted_check;
      reg_vco0_locked_count_threshold        <= reg_vco0_locked_count_threshold;
      reg_vco0_fll_bypass_band               <= reg_vco0_fll_bypass_band;
      reg_vco0_fll_bypass_fine               <= reg_vco0_fll_bypass_fine;
      reg_vco0_fll_persistent_mode           <= reg_vco0_fll_persistent_mode;
    end
  end

  assign VCO0_FLL_CONTROL1_reg_read = {3'h0,
          vco0_locked,
          vco0_too_slow_status,
          vco0_too_fast_status,
          reg_vco0_fll_persistent_mode,
          reg_vco0_fll_bypass_fine,
          reg_vco0_fll_bypass_band,
          reg_vco0_locked_count_threshold,
          reg_vco0_use_demeted_check,
          reg_vco0_delay_count,
          reg_vco0_fine_start,
          reg_vco0_band_start,
          reg_vco0_fll_manual_mode,
          reg_vco0_fll_enable};

  //-----------------------
  assign swi_vco0_fll_enable = reg_vco0_fll_enable;

  //-----------------------
  assign swi_vco0_fll_manual_mode = reg_vco0_fll_manual_mode;

  //-----------------------
  assign swi_vco0_band_start = reg_vco0_band_start;

  //-----------------------
  assign swi_vco0_fine_start = reg_vco0_fine_start;

  //-----------------------
  assign swi_vco0_delay_count = reg_vco0_delay_count;

  //-----------------------
  assign swi_vco0_use_demeted_check = reg_vco0_use_demeted_check;

  //-----------------------
  assign swi_vco0_locked_count_threshold = reg_vco0_locked_count_threshold;

  //-----------------------
  assign swi_vco0_fll_bypass_band = reg_vco0_fll_bypass_band;

  //-----------------------
  assign swi_vco0_fll_bypass_fine = reg_vco0_fll_bypass_fine;

  //-----------------------
  assign swi_vco0_fll_persistent_mode = reg_vco0_fll_persistent_mode;

  //-----------------------
  //-----------------------
  //-----------------------




  //---------------------------
  // VCO0_FLL_CONTROL2
  // vco0_fll_refclk_count - Number of Refclk Cycles to Enable VCO Counter
  // vco0_fll_vco_count_target - Number of expected VCO cycles. Target = (refclk_count * refclk period) / vcoclk period
  // vco0_fll_range - +/- range to be considered in target. Outside range will increment/decrement band setting
  //---------------------------
  wire [31:0] VCO0_FLL_CONTROL2_reg_read;
  reg [7:0]   reg_vco0_fll_refclk_count;
  reg [15:0]  reg_vco0_fll_vco_count_target;
  reg [4:0]   reg_vco0_fll_range;

  always @(posedge RegClk or posedge RegReset) begin
    if(RegReset) begin
      reg_vco0_fll_refclk_count              <= 8'h8;
      reg_vco0_fll_vco_count_target          <= 16'hd0;
      reg_vco0_fll_range                     <= 5'h4;
    end else if(RegAddr == 'h24 && RegWrEn) begin
      reg_vco0_fll_refclk_count              <= RegWrData[7:0];
      reg_vco0_fll_vco_count_target          <= RegWrData[23:8];
      reg_vco0_fll_range                     <= RegWrData[28:24];
    end else begin
      reg_vco0_fll_refclk_count              <= reg_vco0_fll_refclk_count;
      reg_vco0_fll_vco_count_target          <= reg_vco0_fll_vco_count_target;
      reg_vco0_fll_range                     <= reg_vco0_fll_range;
    end
  end

  assign VCO0_FLL_CONTROL2_reg_read = {3'h0,
          reg_vco0_fll_range,
          reg_vco0_fll_vco_count_target,
          reg_vco0_fll_refclk_count};

  //-----------------------
  assign swi_vco0_fll_refclk_count = reg_vco0_fll_refclk_count;

  //-----------------------
  assign swi_vco0_fll_vco_count_target = reg_vco0_fll_vco_count_target;

  //-----------------------
  assign swi_vco0_fll_range = reg_vco0_fll_range;





  //---------------------------
  // VCO0_FLL_CONTROL3
  // vco0_fll_band_thresh - Threshold to indicate that the FLL band is too high
  //---------------------------
  wire [31:0] VCO0_FLL_CONTROL3_reg_read;
  reg [5:0]   reg_vco0_fll_band_thresh;

  always @(posedge RegClk or posedge RegReset) begin
    if(RegReset) begin
      reg_vco0_fll_band_thresh               <= 6'h3c;
    end else if(RegAddr == 'h28 && RegWrEn) begin
      reg_vco0_fll_band_thresh               <= RegWrData[5:0];
    end else begin
      reg_vco0_fll_band_thresh               <= reg_vco0_fll_band_thresh;
    end
  end

  assign VCO0_FLL_CONTROL3_reg_read = {26'h0,
          reg_vco0_fll_band_thresh};

  //-----------------------
  assign swi_vco0_fll_band_thresh = reg_vco0_fll_band_thresh;





  //---------------------------
  // VCO0_FLL_BAND_STATUS
  // vco0_band_status - Latest band reading
  // vco0_band_prev_status - N-1 band reading
  // vco0_fine_status - Latest fine reading
  // vco0_fine_prev_status - N-1 fine reading
  //---------------------------
  wire [31:0] VCO0_FLL_BAND_STATUS_reg_read;
  assign VCO0_FLL_BAND_STATUS_reg_read = {8'h0,
          vco0_fine_prev_status,
          vco0_fine_status,
          vco0_band_prev_status,
          vco0_band_status};

  //-----------------------
  //-----------------------
  //-----------------------
  //-----------------------




  //---------------------------
  // VCO0_FLL_COUNT_STATUS
  // vco0_vco_count - Current VCO count from FLL. To be used for manual calibration
  //---------------------------
  wire [31:0] VCO0_FLL_COUNT_STATUS_reg_read;
  assign VCO0_FLL_COUNT_STATUS_reg_read = {16'h0,
          vco0_vco_count};

  //-----------------------




  //---------------------------
  // VCO0_INT_FRAC_SETTINGS
  // vco0_int - Integer value of feedback divider when VCO is in PLL mode
  // vco0_frac - Fractional value of feedback divider when VCO is in PLL mode
  // vco0_frac_en - 
  // vco0_frac_en_auto - 
  //---------------------------
  wire [31:0] VCO0_INT_FRAC_SETTINGS_reg_read;
  reg [8:0]   reg_vco0_int;
  reg [15:0]  reg_vco0_frac;
  reg         reg_vco0_frac_en;
  reg         reg_vco0_frac_en_auto;

  always @(posedge RegClk or posedge RegReset) begin
    if(RegReset) begin
      reg_vco0_int                           <= 9'ha;
      reg_vco0_frac                          <= 16'h0;
      reg_vco0_frac_en                       <= 1'h0;
      reg_vco0_frac_en_auto                  <= 1'h1;
    end else if(RegAddr == 'h34 && RegWrEn) begin
      reg_vco0_int                           <= RegWrData[8:0];
      reg_vco0_frac                          <= RegWrData[24:9];
      reg_vco0_frac_en                       <= RegWrData[25];
      reg_vco0_frac_en_auto                  <= RegWrData[26];
    end else begin
      reg_vco0_int                           <= reg_vco0_int;
      reg_vco0_frac                          <= reg_vco0_frac;
      reg_vco0_frac_en                       <= reg_vco0_frac_en;
      reg_vco0_frac_en_auto                  <= reg_vco0_frac_en_auto;
    end
  end

  assign VCO0_INT_FRAC_SETTINGS_reg_read = {5'h0,
          reg_vco0_frac_en_auto,
          reg_vco0_frac_en,
          reg_vco0_frac,
          reg_vco0_int};

  //-----------------------
  assign swi_vco0_int = reg_vco0_int;

  //-----------------------
  assign swi_vco0_frac = reg_vco0_frac;

  //-----------------------
  assign swi_vco0_frac_en = reg_vco0_frac_en;

  //-----------------------
  assign swi_vco0_frac_en_auto = reg_vco0_frac_en_auto;





  //---------------------------
  // VCO0_PROP_GAINS
  // vco0_prop_gain - Proportional gain when this VCO is active
  //---------------------------
  wire [31:0] VCO0_PROP_GAINS_reg_read;
  reg [4:0]   reg_vco0_prop_gain;

  always @(posedge RegClk or posedge RegReset) begin
    if(RegReset) begin
      reg_vco0_prop_gain                     <= 5'ha;
    end else if(RegAddr == 'h38 && RegWrEn) begin
      reg_vco0_prop_gain                     <= RegWrData[4:0];
    end else begin
      reg_vco0_prop_gain                     <= reg_vco0_prop_gain;
    end
  end

  assign VCO0_PROP_GAINS_reg_read = {27'h0,
          reg_vco0_prop_gain};

  //-----------------------
  assign swi_vco0_prop_gain = reg_vco0_prop_gain;





  //---------------------------
  // VCO1_BAND
  // vco1_band - Binary representation of VCO band
  // vco1_band_mux - 1 - Use value from register. 0 - Hardware controlled
  // reserved0 - 
  // vco1_fine - VCO Fine Control Value
  // vco1_fine_mux - 1 - Use value from register. 0 - Hardware controlled
  //---------------------------
  wire [31:0] VCO1_BAND_reg_read;
  reg  [5:0]   reg_vco1_band;
  reg  [5:0]   reg_vco1_fine;

  always @(posedge RegClk or posedge RegReset) begin
    if(RegReset) begin
      reg_vco1_band                          <= 6'h0;
      reg_vco1_band_mux                      <= 1'h0;
      reg_vco1_fine                          <= 6'h0;
      reg_vco1_fine_mux                      <= 1'h0;
    end else if(RegAddr == 'h3c && RegWrEn) begin
      reg_vco1_band                          <= RegWrData[5:0];
      reg_vco1_band_mux                      <= RegWrData[6];
      reg_vco1_fine                          <= RegWrData[13:8];
      reg_vco1_fine_mux                      <= RegWrData[14];
    end else begin
      reg_vco1_band                          <= reg_vco1_band;
      reg_vco1_band_mux                      <= reg_vco1_band_mux;
      reg_vco1_fine                          <= reg_vco1_fine;
      reg_vco1_fine_mux                      <= reg_vco1_fine_mux;
    end
  end

  assign VCO1_BAND_reg_read = {17'h0,
          reg_vco1_fine_mux,
          reg_vco1_fine,
          1'd0, //Reserved
          reg_vco1_band_mux,
          reg_vco1_band};

  //-----------------------

  wire [5:0]  swi_vco1_band_muxed_pre;
  wav_clock_mux u_wav_clock_mux_vco1_band[5:0] (
    .clk0    ( vco1_band                          ),              
    .clk1    ( reg_vco1_band                      ),              
    .sel     ( reg_vco1_band_mux                  ),      
    .clk_out ( swi_vco1_band_muxed_pre            )); 

  wire [5:0] vco1_band_tdo;


  wire [5:0] vco1_band_bscan_flop_po;
  mvp_pll_jtag_bsr u_mvp_pll_jtag_bsr_vco1_band[5:0] (   
    .tck        ( dft_bscan_tck                      ),          
    .trst_n     ( dft_bscan_trst_n                   ),      
    .bscan_mode ( dft_bscan_mode                     ),
    .capturedr  ( dft_bscan_capturedr                ),
    .shiftdr    ( dft_bscan_shiftdr                  ),          
    .updatedr   ( dft_bscan_updatedr                 ),               
    .pi         ( swi_vco1_band_muxed_pre            ),               
    .po         ( vco1_band_bscan_flop_po            ),               
    .tdi        ( {vco1_band_tdo[4],
                   vco1_band_tdo[3],
                   vco1_band_tdo[2],
                   vco1_band_tdo[1],
                   vco1_band_tdo[0],
                   vco0_byp_clk_sel_tdo}     ),                
    .tdo        ( {vco1_band_tdo[5],
                   vco1_band_tdo[4],
                   vco1_band_tdo[3],
                   vco1_band_tdo[2],
                   vco1_band_tdo[1],
                   vco1_band_tdo[0]}     )); 

  assign swi_vco1_band_muxed = vco1_band_bscan_flop_po;

  //-----------------------
  //-----------------------
  //-----------------------

  wire [5:0]  swi_vco1_fine_muxed_pre;
  wav_clock_mux u_wav_clock_mux_vco1_fine[5:0] (
    .clk0    ( vco1_fine                          ),              
    .clk1    ( reg_vco1_fine                      ),              
    .sel     ( reg_vco1_fine_mux                  ),      
    .clk_out ( swi_vco1_fine_muxed_pre            )); 

  wire [5:0] vco1_fine_tdo;


  wire [5:0] vco1_fine_bscan_flop_po;
  mvp_pll_jtag_bsr u_mvp_pll_jtag_bsr_vco1_fine[5:0] (   
    .tck        ( dft_bscan_tck                      ),          
    .trst_n     ( dft_bscan_trst_n                   ),      
    .bscan_mode ( dft_bscan_mode                     ),
    .capturedr  ( dft_bscan_capturedr                ),
    .shiftdr    ( dft_bscan_shiftdr                  ),          
    .updatedr   ( dft_bscan_updatedr                 ),               
    .pi         ( swi_vco1_fine_muxed_pre            ),               
    .po         ( vco1_fine_bscan_flop_po            ),               
    .tdi        ( {vco1_fine_tdo[4],
                   vco1_fine_tdo[3],
                   vco1_fine_tdo[2],
                   vco1_fine_tdo[1],
                   vco1_fine_tdo[0],
                   vco1_band_tdo[5]}     ),                
    .tdo        ( {vco1_fine_tdo[5],
                   vco1_fine_tdo[4],
                   vco1_fine_tdo[3],
                   vco1_fine_tdo[2],
                   vco1_fine_tdo[1],
                   vco1_fine_tdo[0]}     )); 

  assign swi_vco1_fine_muxed = vco1_fine_bscan_flop_po;

  //-----------------------




  //---------------------------
  // VCO1_CONTROL
  // vco1_ena - Main Enable of the VCO
  // vco1_ena_mux - 1 - Use value from vco0_ena. 0 - Hardware controlled
  // vco1_byp_clk_sel - Uses refclk for VCO output clock
  // vco1_post_div - 00 - No div, 01 - /2, 10 - /4, 11 - /8
  //---------------------------
  wire [31:0] VCO1_CONTROL_reg_read;
  reg          reg_vco1_ena;
  reg         reg_vco1_byp_clk_sel;
  reg [1:0]   reg_vco1_post_div;

  always @(posedge RegClk or posedge RegReset) begin
    if(RegReset) begin
      reg_vco1_ena                           <= 1'h0;
      reg_vco1_ena_mux                       <= 1'h0;
      reg_vco1_byp_clk_sel                   <= 1'h0;
      reg_vco1_post_div                      <= 2'h0;
    end else if(RegAddr == 'h40 && RegWrEn) begin
      reg_vco1_ena                           <= RegWrData[0];
      reg_vco1_ena_mux                       <= RegWrData[1];
      reg_vco1_byp_clk_sel                   <= RegWrData[2];
      reg_vco1_post_div                      <= RegWrData[4:3];
    end else begin
      reg_vco1_ena                           <= reg_vco1_ena;
      reg_vco1_ena_mux                       <= reg_vco1_ena_mux;
      reg_vco1_byp_clk_sel                   <= reg_vco1_byp_clk_sel;
      reg_vco1_post_div                      <= reg_vco1_post_div;
    end
  end

  assign VCO1_CONTROL_reg_read = {27'h0,
          reg_vco1_post_div,
          reg_vco1_byp_clk_sel,
          reg_vco1_ena_mux,
          reg_vco1_ena};

  //-----------------------

  wire        swi_vco1_ena_muxed_pre;
  wav_clock_mux u_wav_clock_mux_vco1_ena (
    .clk0    ( vco1_ena                           ),              
    .clk1    ( reg_vco1_ena                       ),              
    .sel     ( reg_vco1_ena_mux                   ),      
    .clk_out ( swi_vco1_ena_muxed_pre             )); 


  wire        reg_vco1_ena_core_scan_mode;
  wav_clock_mux u_wav_clock_mux_vco1_ena_core_scan_mode (
    .clk0    ( swi_vco1_ena_muxed_pre             ),              
    .clk1    ( 1'd0                               ),              
    .sel     ( dft_core_scan_mode                 ),      
    .clk_out ( reg_vco1_ena_core_scan_mode        )); 


  wire        reg_vco1_ena_iddq_mode;
  wav_clock_mux u_wav_clock_mux_vco1_ena_iddq_mode (
    .clk0    ( reg_vco1_ena_core_scan_mode        ),              
    .clk1    ( 1'd0                               ),              
    .sel     ( dft_iddq_mode                      ),      
    .clk_out ( reg_vco1_ena_iddq_mode             )); 

  wire  vco1_ena_tdo;


  wire  vco1_ena_bscan_flop_po;
  mvp_pll_jtag_bsr u_mvp_pll_jtag_bsr_vco1_ena (   
    .tck        ( dft_bscan_tck                      ),          
    .trst_n     ( dft_bscan_trst_n                   ),      
    .bscan_mode ( dft_bscan_mode                     ),
    .capturedr  ( dft_bscan_capturedr                ),
    .shiftdr    ( dft_bscan_shiftdr                  ),          
    .updatedr   ( dft_bscan_updatedr                 ),               
    .pi         ( reg_vco1_ena_iddq_mode             ),               
    .po         ( vco1_ena_bscan_flop_po             ),               
    .tdi        ( vco1_fine_tdo[5]                   ),                
    .tdo        ( vco1_ena_tdo                       )); 

  assign swi_vco1_ena_muxed = vco1_ena_bscan_flop_po;

  //-----------------------
  //-----------------------
  wire  vco1_byp_clk_sel_tdo;


  wire  vco1_byp_clk_sel_bscan_flop_po;
  mvp_pll_jtag_bsr u_mvp_pll_jtag_bsr_vco1_byp_clk_sel (   
    .tck        ( dft_bscan_tck                      ),          
    .trst_n     ( dft_bscan_trst_n                   ),      
    .bscan_mode ( dft_bscan_mode                     ),
    .capturedr  ( dft_bscan_capturedr                ),
    .shiftdr    ( dft_bscan_shiftdr                  ),          
    .updatedr   ( dft_bscan_updatedr                 ),               
    .pi         ( reg_vco1_byp_clk_sel               ),               
    .po         ( vco1_byp_clk_sel_bscan_flop_po     ),               
    .tdi        ( vco1_ena_tdo                       ),                
    .tdo        ( vco1_byp_clk_sel_tdo               )); 

  assign swi_vco1_byp_clk_sel = vco1_byp_clk_sel_bscan_flop_po;

  //-----------------------
  wire [1:0] vco1_post_div_tdo;


  wire [1:0] vco1_post_div_bscan_flop_po;
  mvp_pll_jtag_bsr u_mvp_pll_jtag_bsr_vco1_post_div[1:0] (   
    .tck        ( dft_bscan_tck                      ),          
    .trst_n     ( dft_bscan_trst_n                   ),      
    .bscan_mode ( dft_bscan_mode                     ),
    .capturedr  ( dft_bscan_capturedr                ),
    .shiftdr    ( dft_bscan_shiftdr                  ),          
    .updatedr   ( dft_bscan_updatedr                 ),               
    .pi         ( reg_vco1_post_div                  ),               
    .po         ( vco1_post_div_bscan_flop_po        ),               
    .tdi        ( {vco1_post_div_tdo[0],
                   vco1_byp_clk_sel_tdo}     ),                
    .tdo        ( {vco1_post_div_tdo[1],
                   vco1_post_div_tdo[0]}     )); 

  assign swi_vco1_post_div = vco1_post_div_bscan_flop_po;





  //---------------------------
  // VCO1_FLL_CONTROL1
  // vco1_fll_enable - Enables FLL
  // vco1_fll_manual_mode - 0 - FLL will continually change band, 1 - FLL will run once (used for manual SW calibration of band)
  // vco1_band_start - Starting band upon enabling FLL.
  // vco1_fine_start - Starting fine code upon enabling FLL. A mid code is **generally** the expected starting value.
  // vco1_delay_count - Number of Refclk Cycles to wait after deactivation of counters before checking up/dn
  // vco1_use_demeted_check - 1 - up/dn check is based on demeted signals, 0 - up/dn is coming from VCO clock domain (ensure enough delay thorugh delay count)
  // vco1_locked_count_threshold - Number of consecutive cycles where band toggles +/-1 before indicating locked
  // vco1_fll_bypass_band - 1 - Band code is not calibrated during FLL enable. User would want to set the vco_band_start to the desired band setting
  // vco1_fll_bypass_fine - 1 - Fine code is not calibrated during FLL enable. User would want to set the vco_fine_start to the desired band setting
  // vco1_fll_persistent_mode - 0 - FLL will run until lock is detected and will hold code. 1 - FLL will continue to run, adapting to frequency changes. 
  // vco1_too_fast_status - Asserted if VCO count is higher than target + range (use during manual SW calibration)
  // vco1_too_slow_status - Asserted if VCO count is lower than target + range (use during manual SW calibration)
  // vco1_locked - FLL lock indication 
  //---------------------------
  wire [31:0] VCO1_FLL_CONTROL1_reg_read;
  reg         reg_vco1_fll_enable;
  reg         reg_vco1_fll_manual_mode;
  reg [5:0]   reg_vco1_band_start;
  reg [5:0]   reg_vco1_fine_start;
  reg [3:0]   reg_vco1_delay_count;
  reg         reg_vco1_use_demeted_check;
  reg [3:0]   reg_vco1_locked_count_threshold;
  reg         reg_vco1_fll_bypass_band;
  reg         reg_vco1_fll_bypass_fine;
  reg         reg_vco1_fll_persistent_mode;

  always @(posedge RegClk or posedge RegReset) begin
    if(RegReset) begin
      reg_vco1_fll_enable                    <= 1'h0;
      reg_vco1_fll_manual_mode               <= 1'h0;
      reg_vco1_band_start                    <= 6'h0;
      reg_vco1_fine_start                    <= 6'h1f;
      reg_vco1_delay_count                   <= 4'h2;
      reg_vco1_use_demeted_check             <= 1'h1;
      reg_vco1_locked_count_threshold        <= 4'h4;
      reg_vco1_fll_bypass_band               <= 1'h0;
      reg_vco1_fll_bypass_fine               <= 1'h0;
      reg_vco1_fll_persistent_mode           <= 1'h0;
    end else if(RegAddr == 'h44 && RegWrEn) begin
      reg_vco1_fll_enable                    <= RegWrData[0];
      reg_vco1_fll_manual_mode               <= RegWrData[1];
      reg_vco1_band_start                    <= RegWrData[7:2];
      reg_vco1_fine_start                    <= RegWrData[13:8];
      reg_vco1_delay_count                   <= RegWrData[17:14];
      reg_vco1_use_demeted_check             <= RegWrData[18];
      reg_vco1_locked_count_threshold        <= RegWrData[22:19];
      reg_vco1_fll_bypass_band               <= RegWrData[23];
      reg_vco1_fll_bypass_fine               <= RegWrData[24];
      reg_vco1_fll_persistent_mode           <= RegWrData[25];
    end else begin
      reg_vco1_fll_enable                    <= reg_vco1_fll_enable;
      reg_vco1_fll_manual_mode               <= reg_vco1_fll_manual_mode;
      reg_vco1_band_start                    <= reg_vco1_band_start;
      reg_vco1_fine_start                    <= reg_vco1_fine_start;
      reg_vco1_delay_count                   <= reg_vco1_delay_count;
      reg_vco1_use_demeted_check             <= reg_vco1_use_demeted_check;
      reg_vco1_locked_count_threshold        <= reg_vco1_locked_count_threshold;
      reg_vco1_fll_bypass_band               <= reg_vco1_fll_bypass_band;
      reg_vco1_fll_bypass_fine               <= reg_vco1_fll_bypass_fine;
      reg_vco1_fll_persistent_mode           <= reg_vco1_fll_persistent_mode;
    end
  end

  assign VCO1_FLL_CONTROL1_reg_read = {3'h0,
          vco1_locked,
          vco1_too_slow_status,
          vco1_too_fast_status,
          reg_vco1_fll_persistent_mode,
          reg_vco1_fll_bypass_fine,
          reg_vco1_fll_bypass_band,
          reg_vco1_locked_count_threshold,
          reg_vco1_use_demeted_check,
          reg_vco1_delay_count,
          reg_vco1_fine_start,
          reg_vco1_band_start,
          reg_vco1_fll_manual_mode,
          reg_vco1_fll_enable};

  //-----------------------
  assign swi_vco1_fll_enable = reg_vco1_fll_enable;

  //-----------------------
  assign swi_vco1_fll_manual_mode = reg_vco1_fll_manual_mode;

  //-----------------------
  assign swi_vco1_band_start = reg_vco1_band_start;

  //-----------------------
  assign swi_vco1_fine_start = reg_vco1_fine_start;

  //-----------------------
  assign swi_vco1_delay_count = reg_vco1_delay_count;

  //-----------------------
  assign swi_vco1_use_demeted_check = reg_vco1_use_demeted_check;

  //-----------------------
  assign swi_vco1_locked_count_threshold = reg_vco1_locked_count_threshold;

  //-----------------------
  assign swi_vco1_fll_bypass_band = reg_vco1_fll_bypass_band;

  //-----------------------
  assign swi_vco1_fll_bypass_fine = reg_vco1_fll_bypass_fine;

  //-----------------------
  assign swi_vco1_fll_persistent_mode = reg_vco1_fll_persistent_mode;

  //-----------------------
  //-----------------------
  //-----------------------




  //---------------------------
  // VCO1_FLL_CONTROL2
  // vco1_fll_refclk_count - Number of Refclk Cycles to Enable VCO Counter
  // vco1_fll_vco_count_target - Number of expected VCO cycles. Target = (refclk_count * refclk period) / vcoclk period
  // vco1_fll_range - +/- range to be considered in target. Outside range will increment/decrement band setting
  //---------------------------
  wire [31:0] VCO1_FLL_CONTROL2_reg_read;
  reg [7:0]   reg_vco1_fll_refclk_count;
  reg [15:0]  reg_vco1_fll_vco_count_target;
  reg [4:0]   reg_vco1_fll_range;

  always @(posedge RegClk or posedge RegReset) begin
    if(RegReset) begin
      reg_vco1_fll_refclk_count              <= 8'h8;
      reg_vco1_fll_vco_count_target          <= 16'hd0;
      reg_vco1_fll_range                     <= 5'h4;
    end else if(RegAddr == 'h48 && RegWrEn) begin
      reg_vco1_fll_refclk_count              <= RegWrData[7:0];
      reg_vco1_fll_vco_count_target          <= RegWrData[23:8];
      reg_vco1_fll_range                     <= RegWrData[28:24];
    end else begin
      reg_vco1_fll_refclk_count              <= reg_vco1_fll_refclk_count;
      reg_vco1_fll_vco_count_target          <= reg_vco1_fll_vco_count_target;
      reg_vco1_fll_range                     <= reg_vco1_fll_range;
    end
  end

  assign VCO1_FLL_CONTROL2_reg_read = {3'h0,
          reg_vco1_fll_range,
          reg_vco1_fll_vco_count_target,
          reg_vco1_fll_refclk_count};

  //-----------------------
  assign swi_vco1_fll_refclk_count = reg_vco1_fll_refclk_count;

  //-----------------------
  assign swi_vco1_fll_vco_count_target = reg_vco1_fll_vco_count_target;

  //-----------------------
  assign swi_vco1_fll_range = reg_vco1_fll_range;





  //---------------------------
  // VCO1_FLL_CONTROL3
  // vco1_fll_band_thresh - Threshold to indicate that the FLL band is too high
  //---------------------------
  wire [31:0] VCO1_FLL_CONTROL3_reg_read;
  reg [5:0]   reg_vco1_fll_band_thresh;

  always @(posedge RegClk or posedge RegReset) begin
    if(RegReset) begin
      reg_vco1_fll_band_thresh               <= 6'h3c;
    end else if(RegAddr == 'h4c && RegWrEn) begin
      reg_vco1_fll_band_thresh               <= RegWrData[5:0];
    end else begin
      reg_vco1_fll_band_thresh               <= reg_vco1_fll_band_thresh;
    end
  end

  assign VCO1_FLL_CONTROL3_reg_read = {26'h0,
          reg_vco1_fll_band_thresh};

  //-----------------------
  assign swi_vco1_fll_band_thresh = reg_vco1_fll_band_thresh;





  //---------------------------
  // VCO1_FLL_BAND_STATUS
  // vco1_band_status - Latest band reading
  // vco1_band_prev_status - N-1 band reading
  // vco1_fine_status - Latest fine reading
  // vco1_fine_prev_status - N-1 fine reading
  //---------------------------
  wire [31:0] VCO1_FLL_BAND_STATUS_reg_read;
  assign VCO1_FLL_BAND_STATUS_reg_read = {8'h0,
          vco1_fine_prev_status,
          vco1_fine_status,
          vco1_band_prev_status,
          vco1_band_status};

  //-----------------------
  //-----------------------
  //-----------------------
  //-----------------------




  //---------------------------
  // VCO1_FLL_COUNT_STATUS
  // vco1_vco_count - Current VCO count from FLL. To be used for manual calibration
  //---------------------------
  wire [31:0] VCO1_FLL_COUNT_STATUS_reg_read;
  assign VCO1_FLL_COUNT_STATUS_reg_read = {16'h0,
          vco1_vco_count};

  //-----------------------




  //---------------------------
  // VCO1_INT_FRAC_SETTINGS
  // vco1_int - Integer value of feedback divider when VCO is in PLL mode
  // vco1_frac - Fractional value of feedback divider when VCO is in PLL mode
  // vco1_frac_en - 
  // vco1_frac_en_auto - 
  //---------------------------
  wire [31:0] VCO1_INT_FRAC_SETTINGS_reg_read;
  reg [8:0]   reg_vco1_int;
  reg [15:0]  reg_vco1_frac;
  reg         reg_vco1_frac_en;
  reg         reg_vco1_frac_en_auto;

  always @(posedge RegClk or posedge RegReset) begin
    if(RegReset) begin
      reg_vco1_int                           <= 9'ha;
      reg_vco1_frac                          <= 16'h0;
      reg_vco1_frac_en                       <= 1'h0;
      reg_vco1_frac_en_auto                  <= 1'h1;
    end else if(RegAddr == 'h58 && RegWrEn) begin
      reg_vco1_int                           <= RegWrData[8:0];
      reg_vco1_frac                          <= RegWrData[24:9];
      reg_vco1_frac_en                       <= RegWrData[25];
      reg_vco1_frac_en_auto                  <= RegWrData[26];
    end else begin
      reg_vco1_int                           <= reg_vco1_int;
      reg_vco1_frac                          <= reg_vco1_frac;
      reg_vco1_frac_en                       <= reg_vco1_frac_en;
      reg_vco1_frac_en_auto                  <= reg_vco1_frac_en_auto;
    end
  end

  assign VCO1_INT_FRAC_SETTINGS_reg_read = {5'h0,
          reg_vco1_frac_en_auto,
          reg_vco1_frac_en,
          reg_vco1_frac,
          reg_vco1_int};

  //-----------------------
  assign swi_vco1_int = reg_vco1_int;

  //-----------------------
  assign swi_vco1_frac = reg_vco1_frac;

  //-----------------------
  assign swi_vco1_frac_en = reg_vco1_frac_en;

  //-----------------------
  assign swi_vco1_frac_en_auto = reg_vco1_frac_en_auto;





  //---------------------------
  // VCO1_PROP_GAINS
  // vco1_prop_gain - Proportional gain when this VCO is active
  //---------------------------
  wire [31:0] VCO1_PROP_GAINS_reg_read;
  reg [4:0]   reg_vco1_prop_gain;

  always @(posedge RegClk or posedge RegReset) begin
    if(RegReset) begin
      reg_vco1_prop_gain                     <= 5'ha;
    end else if(RegAddr == 'h5c && RegWrEn) begin
      reg_vco1_prop_gain                     <= RegWrData[4:0];
    end else begin
      reg_vco1_prop_gain                     <= reg_vco1_prop_gain;
    end
  end

  assign VCO1_PROP_GAINS_reg_read = {27'h0,
          reg_vco1_prop_gain};

  //-----------------------
  assign swi_vco1_prop_gain = reg_vco1_prop_gain;





  //---------------------------
  // VCO1_SSC_CONTROLS
  // vco1_ssc_enable - 
  // vco1_ssc_stepsize - 
  // vco1_ssc_amp - 
  // vco1_ssc_count_cycles - 
  // vco1_ssc_center_spread - 
  //---------------------------
  wire [31:0] VCO1_SSC_CONTROLS_reg_read;
  reg         reg_vco1_ssc_enable;
  reg [9:0]   reg_vco1_ssc_stepsize;
  reg [16:0]  reg_vco1_ssc_amp;
  reg         reg_vco1_ssc_count_cycles;
  reg         reg_vco1_ssc_center_spread;

  always @(posedge RegClk or posedge RegReset) begin
    if(RegReset) begin
      reg_vco1_ssc_enable                    <= 1'h0;
      reg_vco1_ssc_stepsize                  <= 10'h0;
      reg_vco1_ssc_amp                       <= 17'h0;
      reg_vco1_ssc_count_cycles              <= 1'h0;
      reg_vco1_ssc_center_spread             <= 1'h0;
    end else if(RegAddr == 'h60 && RegWrEn) begin
      reg_vco1_ssc_enable                    <= RegWrData[0];
      reg_vco1_ssc_stepsize                  <= RegWrData[10:1];
      reg_vco1_ssc_amp                       <= RegWrData[27:11];
      reg_vco1_ssc_count_cycles              <= RegWrData[28];
      reg_vco1_ssc_center_spread             <= RegWrData[29];
    end else begin
      reg_vco1_ssc_enable                    <= reg_vco1_ssc_enable;
      reg_vco1_ssc_stepsize                  <= reg_vco1_ssc_stepsize;
      reg_vco1_ssc_amp                       <= reg_vco1_ssc_amp;
      reg_vco1_ssc_count_cycles              <= reg_vco1_ssc_count_cycles;
      reg_vco1_ssc_center_spread             <= reg_vco1_ssc_center_spread;
    end
  end

  assign VCO1_SSC_CONTROLS_reg_read = {2'h0,
          reg_vco1_ssc_center_spread,
          reg_vco1_ssc_count_cycles,
          reg_vco1_ssc_amp,
          reg_vco1_ssc_stepsize,
          reg_vco1_ssc_enable};

  //-----------------------
  assign swi_vco1_ssc_enable = reg_vco1_ssc_enable;

  //-----------------------
  assign swi_vco1_ssc_stepsize = reg_vco1_ssc_stepsize;

  //-----------------------
  assign swi_vco1_ssc_amp = reg_vco1_ssc_amp;

  //-----------------------
  assign swi_vco1_ssc_count_cycles = reg_vco1_ssc_count_cycles;

  //-----------------------
  assign swi_vco1_ssc_center_spread = reg_vco1_ssc_center_spread;





  //---------------------------
  // VCO2_BAND
  // vco2_band - Binary representation of VCO band
  // vco2_band_mux - 1 - Use value from register. 0 - Hardware controlled
  // reserved0 - 
  // vco2_fine - VCO Fine Control Value
  // vco2_fine_mux - 1 - Use value from register. 0 - Hardware controlled
  //---------------------------
  wire [31:0] VCO2_BAND_reg_read;
  reg  [5:0]   reg_vco2_band;
  reg  [5:0]   reg_vco2_fine;

  always @(posedge RegClk or posedge RegReset) begin
    if(RegReset) begin
      reg_vco2_band                          <= 6'h0;
      reg_vco2_band_mux                      <= 1'h0;
      reg_vco2_fine                          <= 6'h0;
      reg_vco2_fine_mux                      <= 1'h0;
    end else if(RegAddr == 'h64 && RegWrEn) begin
      reg_vco2_band                          <= RegWrData[5:0];
      reg_vco2_band_mux                      <= RegWrData[6];
      reg_vco2_fine                          <= RegWrData[13:8];
      reg_vco2_fine_mux                      <= RegWrData[14];
    end else begin
      reg_vco2_band                          <= reg_vco2_band;
      reg_vco2_band_mux                      <= reg_vco2_band_mux;
      reg_vco2_fine                          <= reg_vco2_fine;
      reg_vco2_fine_mux                      <= reg_vco2_fine_mux;
    end
  end

  assign VCO2_BAND_reg_read = {17'h0,
          reg_vco2_fine_mux,
          reg_vco2_fine,
          1'd0, //Reserved
          reg_vco2_band_mux,
          reg_vco2_band};

  //-----------------------

  wire [5:0]  swi_vco2_band_muxed_pre;
  wav_clock_mux u_wav_clock_mux_vco2_band[5:0] (
    .clk0    ( vco2_band                          ),              
    .clk1    ( reg_vco2_band                      ),              
    .sel     ( reg_vco2_band_mux                  ),      
    .clk_out ( swi_vco2_band_muxed_pre            )); 

  wire [5:0] vco2_band_tdo;


  wire [5:0] vco2_band_bscan_flop_po;
  mvp_pll_jtag_bsr u_mvp_pll_jtag_bsr_vco2_band[5:0] (   
    .tck        ( dft_bscan_tck                      ),          
    .trst_n     ( dft_bscan_trst_n                   ),      
    .bscan_mode ( dft_bscan_mode                     ),
    .capturedr  ( dft_bscan_capturedr                ),
    .shiftdr    ( dft_bscan_shiftdr                  ),          
    .updatedr   ( dft_bscan_updatedr                 ),               
    .pi         ( swi_vco2_band_muxed_pre            ),               
    .po         ( vco2_band_bscan_flop_po            ),               
    .tdi        ( {vco2_band_tdo[4],
                   vco2_band_tdo[3],
                   vco2_band_tdo[2],
                   vco2_band_tdo[1],
                   vco2_band_tdo[0],
                   vco1_post_div_tdo[1]}     ),                
    .tdo        ( {vco2_band_tdo[5],
                   vco2_band_tdo[4],
                   vco2_band_tdo[3],
                   vco2_band_tdo[2],
                   vco2_band_tdo[1],
                   vco2_band_tdo[0]}     )); 

  assign swi_vco2_band_muxed = vco2_band_bscan_flop_po;

  //-----------------------
  //-----------------------
  //-----------------------

  wire [5:0]  swi_vco2_fine_muxed_pre;
  wav_clock_mux u_wav_clock_mux_vco2_fine[5:0] (
    .clk0    ( vco2_fine                          ),              
    .clk1    ( reg_vco2_fine                      ),              
    .sel     ( reg_vco2_fine_mux                  ),      
    .clk_out ( swi_vco2_fine_muxed_pre            )); 

  wire [5:0] vco2_fine_tdo;


  wire [5:0] vco2_fine_bscan_flop_po;
  mvp_pll_jtag_bsr u_mvp_pll_jtag_bsr_vco2_fine[5:0] (   
    .tck        ( dft_bscan_tck                      ),          
    .trst_n     ( dft_bscan_trst_n                   ),      
    .bscan_mode ( dft_bscan_mode                     ),
    .capturedr  ( dft_bscan_capturedr                ),
    .shiftdr    ( dft_bscan_shiftdr                  ),          
    .updatedr   ( dft_bscan_updatedr                 ),               
    .pi         ( swi_vco2_fine_muxed_pre            ),               
    .po         ( vco2_fine_bscan_flop_po            ),               
    .tdi        ( {vco2_fine_tdo[4],
                   vco2_fine_tdo[3],
                   vco2_fine_tdo[2],
                   vco2_fine_tdo[1],
                   vco2_fine_tdo[0],
                   vco2_band_tdo[5]}     ),                
    .tdo        ( {vco2_fine_tdo[5],
                   vco2_fine_tdo[4],
                   vco2_fine_tdo[3],
                   vco2_fine_tdo[2],
                   vco2_fine_tdo[1],
                   vco2_fine_tdo[0]}     )); 

  assign swi_vco2_fine_muxed = vco2_fine_bscan_flop_po;

  //-----------------------




  //---------------------------
  // VCO2_CONTROL
  // vco2_ena - Main Enable of the VCO
  // vco2_ena_mux - 1 - Use value from vco2_ena. 0 - Hardware controlled
  // vco2_byp_clk_sel - Uses refclk for VCO output clock
  // vco2_post_div - 00 - No div, 01 - /2, 10 - /4, 11 - /8
  //---------------------------
  wire [31:0] VCO2_CONTROL_reg_read;
  reg          reg_vco2_ena;
  reg         reg_vco2_byp_clk_sel;
  reg [1:0]   reg_vco2_post_div;

  always @(posedge RegClk or posedge RegReset) begin
    if(RegReset) begin
      reg_vco2_ena                           <= 1'h0;
      reg_vco2_ena_mux                       <= 1'h0;
      reg_vco2_byp_clk_sel                   <= 1'h0;
      reg_vco2_post_div                      <= 2'h0;
    end else if(RegAddr == 'h68 && RegWrEn) begin
      reg_vco2_ena                           <= RegWrData[0];
      reg_vco2_ena_mux                       <= RegWrData[1];
      reg_vco2_byp_clk_sel                   <= RegWrData[2];
      reg_vco2_post_div                      <= RegWrData[4:3];
    end else begin
      reg_vco2_ena                           <= reg_vco2_ena;
      reg_vco2_ena_mux                       <= reg_vco2_ena_mux;
      reg_vco2_byp_clk_sel                   <= reg_vco2_byp_clk_sel;
      reg_vco2_post_div                      <= reg_vco2_post_div;
    end
  end

  assign VCO2_CONTROL_reg_read = {27'h0,
          reg_vco2_post_div,
          reg_vco2_byp_clk_sel,
          reg_vco2_ena_mux,
          reg_vco2_ena};

  //-----------------------

  wire        swi_vco2_ena_muxed_pre;
  wav_clock_mux u_wav_clock_mux_vco2_ena (
    .clk0    ( vco2_ena                           ),              
    .clk1    ( reg_vco2_ena                       ),              
    .sel     ( reg_vco2_ena_mux                   ),      
    .clk_out ( swi_vco2_ena_muxed_pre             )); 


  wire        reg_vco2_ena_core_scan_mode;
  wav_clock_mux u_wav_clock_mux_vco2_ena_core_scan_mode (
    .clk0    ( swi_vco2_ena_muxed_pre             ),              
    .clk1    ( 1'd0                               ),              
    .sel     ( dft_core_scan_mode                 ),      
    .clk_out ( reg_vco2_ena_core_scan_mode        )); 


  wire        reg_vco2_ena_iddq_mode;
  wav_clock_mux u_wav_clock_mux_vco2_ena_iddq_mode (
    .clk0    ( reg_vco2_ena_core_scan_mode        ),              
    .clk1    ( 1'd0                               ),              
    .sel     ( dft_iddq_mode                      ),      
    .clk_out ( reg_vco2_ena_iddq_mode             )); 

  wire  vco2_ena_tdo;


  wire  vco2_ena_bscan_flop_po;
  mvp_pll_jtag_bsr u_mvp_pll_jtag_bsr_vco2_ena (   
    .tck        ( dft_bscan_tck                      ),          
    .trst_n     ( dft_bscan_trst_n                   ),      
    .bscan_mode ( dft_bscan_mode                     ),
    .capturedr  ( dft_bscan_capturedr                ),
    .shiftdr    ( dft_bscan_shiftdr                  ),          
    .updatedr   ( dft_bscan_updatedr                 ),               
    .pi         ( reg_vco2_ena_iddq_mode             ),               
    .po         ( vco2_ena_bscan_flop_po             ),               
    .tdi        ( vco2_fine_tdo[5]                   ),                
    .tdo        ( vco2_ena_tdo                       )); 

  assign swi_vco2_ena_muxed = vco2_ena_bscan_flop_po;

  //-----------------------
  //-----------------------
  wire  vco2_byp_clk_sel_tdo;


  wire  vco2_byp_clk_sel_bscan_flop_po;
  mvp_pll_jtag_bsr u_mvp_pll_jtag_bsr_vco2_byp_clk_sel (   
    .tck        ( dft_bscan_tck                      ),          
    .trst_n     ( dft_bscan_trst_n                   ),      
    .bscan_mode ( dft_bscan_mode                     ),
    .capturedr  ( dft_bscan_capturedr                ),
    .shiftdr    ( dft_bscan_shiftdr                  ),          
    .updatedr   ( dft_bscan_updatedr                 ),               
    .pi         ( reg_vco2_byp_clk_sel               ),               
    .po         ( vco2_byp_clk_sel_bscan_flop_po     ),               
    .tdi        ( vco2_ena_tdo                       ),                
    .tdo        ( vco2_byp_clk_sel_tdo               )); 

  assign swi_vco2_byp_clk_sel = vco2_byp_clk_sel_bscan_flop_po;

  //-----------------------
  wire [1:0] vco2_post_div_tdo;


  wire [1:0] vco2_post_div_bscan_flop_po;
  mvp_pll_jtag_bsr u_mvp_pll_jtag_bsr_vco2_post_div[1:0] (   
    .tck        ( dft_bscan_tck                      ),          
    .trst_n     ( dft_bscan_trst_n                   ),      
    .bscan_mode ( dft_bscan_mode                     ),
    .capturedr  ( dft_bscan_capturedr                ),
    .shiftdr    ( dft_bscan_shiftdr                  ),          
    .updatedr   ( dft_bscan_updatedr                 ),               
    .pi         ( reg_vco2_post_div                  ),               
    .po         ( vco2_post_div_bscan_flop_po        ),               
    .tdi        ( {vco2_post_div_tdo[0],
                   vco2_byp_clk_sel_tdo}     ),                
    .tdo        ( {vco2_post_div_tdo[1],
                   vco2_post_div_tdo[0]}     )); 

  assign swi_vco2_post_div = vco2_post_div_bscan_flop_po;





  //---------------------------
  // VCO2_FLL_CONTROL1
  // vco2_fll_enable - Enables FLL
  // vco2_fll_manual_mode - 0 - FLL will continually change band, 1 - FLL will run once (used for manual SW calibration of band)
  // vco2_band_start - Starting band upon enabling FLL.
  // vco2_fine_start - Starting fine code upon enabling FLL. A mid code is **generally** the expected starting value.
  // vco2_delay_count - Number of Refclk Cycles to wait after deactivation of counters before checking up/dn
  // vco2_use_demeted_check - 1 - up/dn check is based on demeted signals, 0 - up/dn is coming from VCO clock domain (ensure enough delay thorugh delay count)
  // vco2_locked_count_threshold - Number of consecutive cycles where band toggles +/-1 before indicating locked
  // vco2_fll_bypass_band - 1 - Band code is not calibrated during FLL enable. User would want to set the vco_band_start to the desired band setting
  // vco2_fll_bypass_fine - 1 - Fine code is not calibrated during FLL enable. User would want to set the vco_fine_start to the desired band setting
  // vco2_fll_persistent_mode - 0 - FLL will run until lock is detected and will hold code. 1 - FLL will continue to run, adapting to frequency changes. 
  // vco2_too_fast_status - Asserted if VCO count is higher than target + range (use during manual SW calibration)
  // vco2_too_slow_status - Asserted if VCO count is lower than target + range (use during manual SW calibration)
  // vco2_locked - FLL lock indication 
  //---------------------------
  wire [31:0] VCO2_FLL_CONTROL1_reg_read;
  reg         reg_vco2_fll_enable;
  reg         reg_vco2_fll_manual_mode;
  reg [5:0]   reg_vco2_band_start;
  reg [5:0]   reg_vco2_fine_start;
  reg [3:0]   reg_vco2_delay_count;
  reg         reg_vco2_use_demeted_check;
  reg [3:0]   reg_vco2_locked_count_threshold;
  reg         reg_vco2_fll_bypass_band;
  reg         reg_vco2_fll_bypass_fine;
  reg         reg_vco2_fll_persistent_mode;

  always @(posedge RegClk or posedge RegReset) begin
    if(RegReset) begin
      reg_vco2_fll_enable                    <= 1'h0;
      reg_vco2_fll_manual_mode               <= 1'h0;
      reg_vco2_band_start                    <= 6'h0;
      reg_vco2_fine_start                    <= 6'h1f;
      reg_vco2_delay_count                   <= 4'h2;
      reg_vco2_use_demeted_check             <= 1'h1;
      reg_vco2_locked_count_threshold        <= 4'h4;
      reg_vco2_fll_bypass_band               <= 1'h0;
      reg_vco2_fll_bypass_fine               <= 1'h0;
      reg_vco2_fll_persistent_mode           <= 1'h0;
    end else if(RegAddr == 'h6c && RegWrEn) begin
      reg_vco2_fll_enable                    <= RegWrData[0];
      reg_vco2_fll_manual_mode               <= RegWrData[1];
      reg_vco2_band_start                    <= RegWrData[7:2];
      reg_vco2_fine_start                    <= RegWrData[13:8];
      reg_vco2_delay_count                   <= RegWrData[17:14];
      reg_vco2_use_demeted_check             <= RegWrData[18];
      reg_vco2_locked_count_threshold        <= RegWrData[22:19];
      reg_vco2_fll_bypass_band               <= RegWrData[23];
      reg_vco2_fll_bypass_fine               <= RegWrData[24];
      reg_vco2_fll_persistent_mode           <= RegWrData[25];
    end else begin
      reg_vco2_fll_enable                    <= reg_vco2_fll_enable;
      reg_vco2_fll_manual_mode               <= reg_vco2_fll_manual_mode;
      reg_vco2_band_start                    <= reg_vco2_band_start;
      reg_vco2_fine_start                    <= reg_vco2_fine_start;
      reg_vco2_delay_count                   <= reg_vco2_delay_count;
      reg_vco2_use_demeted_check             <= reg_vco2_use_demeted_check;
      reg_vco2_locked_count_threshold        <= reg_vco2_locked_count_threshold;
      reg_vco2_fll_bypass_band               <= reg_vco2_fll_bypass_band;
      reg_vco2_fll_bypass_fine               <= reg_vco2_fll_bypass_fine;
      reg_vco2_fll_persistent_mode           <= reg_vco2_fll_persistent_mode;
    end
  end

  assign VCO2_FLL_CONTROL1_reg_read = {3'h0,
          vco2_locked,
          vco2_too_slow_status,
          vco2_too_fast_status,
          reg_vco2_fll_persistent_mode,
          reg_vco2_fll_bypass_fine,
          reg_vco2_fll_bypass_band,
          reg_vco2_locked_count_threshold,
          reg_vco2_use_demeted_check,
          reg_vco2_delay_count,
          reg_vco2_fine_start,
          reg_vco2_band_start,
          reg_vco2_fll_manual_mode,
          reg_vco2_fll_enable};

  //-----------------------
  assign swi_vco2_fll_enable = reg_vco2_fll_enable;

  //-----------------------
  assign swi_vco2_fll_manual_mode = reg_vco2_fll_manual_mode;

  //-----------------------
  assign swi_vco2_band_start = reg_vco2_band_start;

  //-----------------------
  assign swi_vco2_fine_start = reg_vco2_fine_start;

  //-----------------------
  assign swi_vco2_delay_count = reg_vco2_delay_count;

  //-----------------------
  assign swi_vco2_use_demeted_check = reg_vco2_use_demeted_check;

  //-----------------------
  assign swi_vco2_locked_count_threshold = reg_vco2_locked_count_threshold;

  //-----------------------
  assign swi_vco2_fll_bypass_band = reg_vco2_fll_bypass_band;

  //-----------------------
  assign swi_vco2_fll_bypass_fine = reg_vco2_fll_bypass_fine;

  //-----------------------
  assign swi_vco2_fll_persistent_mode = reg_vco2_fll_persistent_mode;

  //-----------------------
  //-----------------------
  //-----------------------




  //---------------------------
  // VCO2_FLL_CONTROL2
  // vco2_fll_refclk_count - Number of Refclk Cycles to Enable VCO Counter
  // vco2_fll_vco_count_target - Number of expected VCO cycles. Target = (refclk_count * refclk period) / vcoclk period
  // vco2_fll_range - +/- range to be considered in target. Outside range will increment/decrement band setting
  //---------------------------
  wire [31:0] VCO2_FLL_CONTROL2_reg_read;
  reg [7:0]   reg_vco2_fll_refclk_count;
  reg [15:0]  reg_vco2_fll_vco_count_target;
  reg [4:0]   reg_vco2_fll_range;

  always @(posedge RegClk or posedge RegReset) begin
    if(RegReset) begin
      reg_vco2_fll_refclk_count              <= 8'h8;
      reg_vco2_fll_vco_count_target          <= 16'hd0;
      reg_vco2_fll_range                     <= 5'h4;
    end else if(RegAddr == 'h70 && RegWrEn) begin
      reg_vco2_fll_refclk_count              <= RegWrData[7:0];
      reg_vco2_fll_vco_count_target          <= RegWrData[23:8];
      reg_vco2_fll_range                     <= RegWrData[28:24];
    end else begin
      reg_vco2_fll_refclk_count              <= reg_vco2_fll_refclk_count;
      reg_vco2_fll_vco_count_target          <= reg_vco2_fll_vco_count_target;
      reg_vco2_fll_range                     <= reg_vco2_fll_range;
    end
  end

  assign VCO2_FLL_CONTROL2_reg_read = {3'h0,
          reg_vco2_fll_range,
          reg_vco2_fll_vco_count_target,
          reg_vco2_fll_refclk_count};

  //-----------------------
  assign swi_vco2_fll_refclk_count = reg_vco2_fll_refclk_count;

  //-----------------------
  assign swi_vco2_fll_vco_count_target = reg_vco2_fll_vco_count_target;

  //-----------------------
  assign swi_vco2_fll_range = reg_vco2_fll_range;





  //---------------------------
  // VCO2_FLL_CONTROL3
  // vco2_fll_band_thresh - Threshold to indicate that the FLL band is too high
  //---------------------------
  wire [31:0] VCO2_FLL_CONTROL3_reg_read;
  reg [5:0]   reg_vco2_fll_band_thresh;

  always @(posedge RegClk or posedge RegReset) begin
    if(RegReset) begin
      reg_vco2_fll_band_thresh               <= 6'h3c;
    end else if(RegAddr == 'h74 && RegWrEn) begin
      reg_vco2_fll_band_thresh               <= RegWrData[5:0];
    end else begin
      reg_vco2_fll_band_thresh               <= reg_vco2_fll_band_thresh;
    end
  end

  assign VCO2_FLL_CONTROL3_reg_read = {26'h0,
          reg_vco2_fll_band_thresh};

  //-----------------------
  assign swi_vco2_fll_band_thresh = reg_vco2_fll_band_thresh;





  //---------------------------
  // VCO2_FLL_BAND_STATUS
  // vco2_band_status - Latest band reading
  // vco2_band_prev_status - N-1 band reading
  // vco2_fine_status - Latest fine reading
  // vco2_fine_prev_status - N-1 fine reading
  //---------------------------
  wire [31:0] VCO2_FLL_BAND_STATUS_reg_read;
  assign VCO2_FLL_BAND_STATUS_reg_read = {8'h0,
          vco2_fine_prev_status,
          vco2_fine_status,
          vco2_band_prev_status,
          vco2_band_status};

  //-----------------------
  //-----------------------
  //-----------------------
  //-----------------------




  //---------------------------
  // VCO2_FLL_COUNT_STATUS
  // vco2_vco_count - Current VCO count from FLL. To be used for manual calibration
  //---------------------------
  wire [31:0] VCO2_FLL_COUNT_STATUS_reg_read;
  assign VCO2_FLL_COUNT_STATUS_reg_read = {16'h0,
          vco2_vco_count};

  //-----------------------




  //---------------------------
  // VCO2_INT_FRAC_SETTINGS
  // vco2_int - Integer value of feedback divider when VCO is in PLL mode
  // vco2_frac - Fractional value of feedback divider when VCO is in PLL mode
  // vco2_frac_en - 
  // vco2_frac_en_auto - 
  //---------------------------
  wire [31:0] VCO2_INT_FRAC_SETTINGS_reg_read;
  reg [8:0]   reg_vco2_int;
  reg [15:0]  reg_vco2_frac;
  reg         reg_vco2_frac_en;
  reg         reg_vco2_frac_en_auto;

  always @(posedge RegClk or posedge RegReset) begin
    if(RegReset) begin
      reg_vco2_int                           <= 9'ha;
      reg_vco2_frac                          <= 16'h0;
      reg_vco2_frac_en                       <= 1'h0;
      reg_vco2_frac_en_auto                  <= 1'h1;
    end else if(RegAddr == 'h80 && RegWrEn) begin
      reg_vco2_int                           <= RegWrData[8:0];
      reg_vco2_frac                          <= RegWrData[24:9];
      reg_vco2_frac_en                       <= RegWrData[25];
      reg_vco2_frac_en_auto                  <= RegWrData[26];
    end else begin
      reg_vco2_int                           <= reg_vco2_int;
      reg_vco2_frac                          <= reg_vco2_frac;
      reg_vco2_frac_en                       <= reg_vco2_frac_en;
      reg_vco2_frac_en_auto                  <= reg_vco2_frac_en_auto;
    end
  end

  assign VCO2_INT_FRAC_SETTINGS_reg_read = {5'h0,
          reg_vco2_frac_en_auto,
          reg_vco2_frac_en,
          reg_vco2_frac,
          reg_vco2_int};

  //-----------------------
  assign swi_vco2_int = reg_vco2_int;

  //-----------------------
  assign swi_vco2_frac = reg_vco2_frac;

  //-----------------------
  assign swi_vco2_frac_en = reg_vco2_frac_en;

  //-----------------------
  assign swi_vco2_frac_en_auto = reg_vco2_frac_en_auto;





  //---------------------------
  // VCO2_PROP_GAINS
  // vco2_prop_gain - Proportional gain when this VCO is active
  //---------------------------
  wire [31:0] VCO2_PROP_GAINS_reg_read;
  reg [4:0]   reg_vco2_prop_gain;

  always @(posedge RegClk or posedge RegReset) begin
    if(RegReset) begin
      reg_vco2_prop_gain                     <= 5'ha;
    end else if(RegAddr == 'h84 && RegWrEn) begin
      reg_vco2_prop_gain                     <= RegWrData[4:0];
    end else begin
      reg_vco2_prop_gain                     <= reg_vco2_prop_gain;
    end
  end

  assign VCO2_PROP_GAINS_reg_read = {27'h0,
          reg_vco2_prop_gain};

  //-----------------------
  assign swi_vco2_prop_gain = reg_vco2_prop_gain;





  //---------------------------
  // VCO2_SSC_CONTROLS
  // vco2_ssc_enable - 
  // vco2_ssc_stepsize - 
  // vco2_ssc_amp - 
  // vco2_ssc_count_cycles - 
  // vco2_ssc_center_spread - 
  //---------------------------
  wire [31:0] VCO2_SSC_CONTROLS_reg_read;
  reg         reg_vco2_ssc_enable;
  reg [9:0]   reg_vco2_ssc_stepsize;
  reg [16:0]  reg_vco2_ssc_amp;
  reg         reg_vco2_ssc_count_cycles;
  reg         reg_vco2_ssc_center_spread;

  always @(posedge RegClk or posedge RegReset) begin
    if(RegReset) begin
      reg_vco2_ssc_enable                    <= 1'h0;
      reg_vco2_ssc_stepsize                  <= 10'h0;
      reg_vco2_ssc_amp                       <= 17'h0;
      reg_vco2_ssc_count_cycles              <= 1'h0;
      reg_vco2_ssc_center_spread             <= 1'h0;
    end else if(RegAddr == 'h88 && RegWrEn) begin
      reg_vco2_ssc_enable                    <= RegWrData[0];
      reg_vco2_ssc_stepsize                  <= RegWrData[10:1];
      reg_vco2_ssc_amp                       <= RegWrData[27:11];
      reg_vco2_ssc_count_cycles              <= RegWrData[28];
      reg_vco2_ssc_center_spread             <= RegWrData[29];
    end else begin
      reg_vco2_ssc_enable                    <= reg_vco2_ssc_enable;
      reg_vco2_ssc_stepsize                  <= reg_vco2_ssc_stepsize;
      reg_vco2_ssc_amp                       <= reg_vco2_ssc_amp;
      reg_vco2_ssc_count_cycles              <= reg_vco2_ssc_count_cycles;
      reg_vco2_ssc_center_spread             <= reg_vco2_ssc_center_spread;
    end
  end

  assign VCO2_SSC_CONTROLS_reg_read = {2'h0,
          reg_vco2_ssc_center_spread,
          reg_vco2_ssc_count_cycles,
          reg_vco2_ssc_amp,
          reg_vco2_ssc_stepsize,
          reg_vco2_ssc_enable};

  //-----------------------
  assign swi_vco2_ssc_enable = reg_vco2_ssc_enable;

  //-----------------------
  assign swi_vco2_ssc_stepsize = reg_vco2_ssc_stepsize;

  //-----------------------
  assign swi_vco2_ssc_amp = reg_vco2_ssc_amp;

  //-----------------------
  assign swi_vco2_ssc_count_cycles = reg_vco2_ssc_count_cycles;

  //-----------------------
  assign swi_vco2_ssc_center_spread = reg_vco2_ssc_center_spread;





  //---------------------------
  // STATE_MACHINE_CONTROLS
  // bias_settle_count - Number of refclk cycles to wait until entering the fastlock routine
  // pre_locking_count - Number of refclk cycles to wait until entering normal lock after fast lock
  // switch_count - Number of refclk cycles to wait with FBCLK disabled when performing a VCO switch
  // disable_lock_det_after_lock - 1 - Lock Detection circuit is disabled after lock is seen. 0 - Lock detection always enabled. Disabling lock detect would mean loss of lock is not possible to detect.
  // fll_initial_settle - Initial settle time for FLLs when enabling. Provides some time for the VCO to ramp up.
  //---------------------------
  wire [31:0] STATE_MACHINE_CONTROLS_reg_read;
  reg [7:0]   reg_bias_settle_count;
  reg [7:0]   reg_pre_locking_count;
  reg [3:0]   reg_switch_count;
  reg         reg_disable_lock_det_after_lock;
  reg [3:0]   reg_fll_initial_settle;

  always @(posedge RegClk or posedge RegReset) begin
    if(RegReset) begin
      reg_bias_settle_count                  <= 8'h8;
      reg_pre_locking_count                  <= 8'h4;
      reg_switch_count                       <= 4'h1;
      reg_disable_lock_det_after_lock        <= 1'h0;
      reg_fll_initial_settle                 <= 4'h4;
    end else if(RegAddr == 'h8c && RegWrEn) begin
      reg_bias_settle_count                  <= RegWrData[7:0];
      reg_pre_locking_count                  <= RegWrData[15:8];
      reg_switch_count                       <= RegWrData[19:16];
      reg_disable_lock_det_after_lock        <= RegWrData[20];
      reg_fll_initial_settle                 <= RegWrData[24:21];
    end else begin
      reg_bias_settle_count                  <= reg_bias_settle_count;
      reg_pre_locking_count                  <= reg_pre_locking_count;
      reg_switch_count                       <= reg_switch_count;
      reg_disable_lock_det_after_lock        <= reg_disable_lock_det_after_lock;
      reg_fll_initial_settle                 <= reg_fll_initial_settle;
    end
  end

  assign STATE_MACHINE_CONTROLS_reg_read = {7'h0,
          reg_fll_initial_settle,
          reg_disable_lock_det_after_lock,
          reg_switch_count,
          reg_pre_locking_count,
          reg_bias_settle_count};

  //-----------------------
  assign swi_bias_settle_count = reg_bias_settle_count;

  //-----------------------
  assign swi_pre_locking_count = reg_pre_locking_count;

  //-----------------------
  assign swi_switch_count = reg_switch_count;

  //-----------------------
  assign swi_disable_lock_det_after_lock = reg_disable_lock_det_after_lock;

  //-----------------------
  assign swi_fll_initial_settle = reg_fll_initial_settle;





  //---------------------------
  // STATE_MACHINE_CONTROLS2
  // pre_switch_time - Number of cycles prior to enabling the next VCO to disable the FBCLK
  // switch_reset_time - Number of cycles to hold the PLL PFD in reset to allow VCO swtich
  // switch_1_time - Number of cycles to the next VCO is allowed to be in PLL mode before switching the clock mux. Increasing this can allow the VCO more time to phase lock before swtiching the clock mux.
  // switch_2_time - Number of cycles to hold both VCOs enabled after the clock mux switch.
  //---------------------------
  wire [31:0] STATE_MACHINE_CONTROLS2_reg_read;
  reg [3:0]   reg_pre_switch_time;
  reg [3:0]   reg_switch_reset_time;
  reg [7:0]   reg_switch_1_time;
  reg [7:0]   reg_switch_2_time;

  always @(posedge RegClk or posedge RegReset) begin
    if(RegReset) begin
      reg_pre_switch_time                    <= 4'h1;
      reg_switch_reset_time                  <= 4'h1;
      reg_switch_1_time                      <= 8'h3;
      reg_switch_2_time                      <= 8'h1;
    end else if(RegAddr == 'h90 && RegWrEn) begin
      reg_pre_switch_time                    <= RegWrData[3:0];
      reg_switch_reset_time                  <= RegWrData[7:4];
      reg_switch_1_time                      <= RegWrData[15:8];
      reg_switch_2_time                      <= RegWrData[23:16];
    end else begin
      reg_pre_switch_time                    <= reg_pre_switch_time;
      reg_switch_reset_time                  <= reg_switch_reset_time;
      reg_switch_1_time                      <= reg_switch_1_time;
      reg_switch_2_time                      <= reg_switch_2_time;
    end
  end

  assign STATE_MACHINE_CONTROLS2_reg_read = {8'h0,
          reg_switch_2_time,
          reg_switch_1_time,
          reg_switch_reset_time,
          reg_pre_switch_time};

  //-----------------------
  assign swi_pre_switch_time = reg_pre_switch_time;

  //-----------------------
  assign swi_switch_reset_time = reg_switch_reset_time;

  //-----------------------
  assign swi_switch_1_time = reg_switch_1_time;

  //-----------------------
  assign swi_switch_2_time = reg_switch_2_time;





  //---------------------------
  // INTR_GAINS
  // normal_int_gain - Integral Gain when not in fastlock
  //---------------------------
  wire [31:0] INTR_GAINS_reg_read;
  reg [4:0]   reg_normal_int_gain;

  always @(posedge RegClk or posedge RegReset) begin
    if(RegReset) begin
      reg_normal_int_gain                    <= 5'hf;
    end else if(RegAddr == 'h94 && RegWrEn) begin
      reg_normal_int_gain                    <= RegWrData[4:0];
    end else begin
      reg_normal_int_gain                    <= reg_normal_int_gain;
    end
  end

  assign INTR_GAINS_reg_read = {27'h0,
          reg_normal_int_gain};

  //-----------------------
  assign swi_normal_int_gain = reg_normal_int_gain;





  //---------------------------
  // INTR_PROP_FL_GAINS
  // fl_int_gain - Integral gain when in fastlock
  // fl_prop_gain - Proportional gain when in fastlock
  //---------------------------
  wire [31:0] INTR_PROP_FL_GAINS_reg_read;
  reg [4:0]   reg_fl_int_gain;
  reg [4:0]   reg_fl_prop_gain;

  always @(posedge RegClk or posedge RegReset) begin
    if(RegReset) begin
      reg_fl_int_gain                        <= 5'h1e;
      reg_fl_prop_gain                       <= 5'h1e;
    end else if(RegAddr == 'h98 && RegWrEn) begin
      reg_fl_int_gain                        <= RegWrData[4:0];
      reg_fl_prop_gain                       <= RegWrData[9:5];
    end else begin
      reg_fl_int_gain                        <= reg_fl_int_gain;
      reg_fl_prop_gain                       <= reg_fl_prop_gain;
    end
  end

  assign INTR_PROP_FL_GAINS_reg_read = {22'h0,
          reg_fl_prop_gain,
          reg_fl_int_gain};

  //-----------------------
  assign swi_fl_int_gain = reg_fl_int_gain;

  //-----------------------
  assign swi_fl_prop_gain = reg_fl_prop_gain;





  //---------------------------
  // INTR_PROP_GAINS_OVERRIDE
  // int_gain - Integral gain directly after VCO switch
  // int_gain_mux - 
  // prop_gain - Proportional gain directly after VCO switch
  // prop_gain_mux - 
  //---------------------------
  wire [31:0] INTR_PROP_GAINS_OVERRIDE_reg_read;
  reg  [4:0]   reg_int_gain;
  reg  [4:0]   reg_prop_gain;

  always @(posedge RegClk or posedge RegReset) begin
    if(RegReset) begin
      reg_int_gain                           <= 5'hf;
      reg_int_gain_mux                       <= 1'h0;
      reg_prop_gain                          <= 5'h9;
      reg_prop_gain_mux                      <= 1'h0;
    end else if(RegAddr == 'h9c && RegWrEn) begin
      reg_int_gain                           <= RegWrData[4:0];
      reg_int_gain_mux                       <= RegWrData[5];
      reg_prop_gain                          <= RegWrData[10:6];
      reg_prop_gain_mux                      <= RegWrData[11];
    end else begin
      reg_int_gain                           <= reg_int_gain;
      reg_int_gain_mux                       <= reg_int_gain_mux;
      reg_prop_gain                          <= reg_prop_gain;
      reg_prop_gain_mux                      <= reg_prop_gain_mux;
    end
  end

  assign INTR_PROP_GAINS_OVERRIDE_reg_read = {20'h0,
          reg_prop_gain_mux,
          reg_prop_gain,
          reg_int_gain_mux,
          reg_int_gain};

  //-----------------------

  wire [4:0]  swi_int_gain_muxed_pre;
  wav_clock_mux u_wav_clock_mux_int_gain[4:0] (
    .clk0    ( int_gain                           ),              
    .clk1    ( reg_int_gain                       ),              
    .sel     ( reg_int_gain_mux                   ),      
    .clk_out ( swi_int_gain_muxed_pre             )); 

  wire [4:0] int_gain_tdo;


  wire [4:0] int_gain_bscan_flop_po;
  mvp_pll_jtag_bsr u_mvp_pll_jtag_bsr_int_gain[4:0] (   
    .tck        ( dft_bscan_tck                      ),          
    .trst_n     ( dft_bscan_trst_n                   ),      
    .bscan_mode ( dft_bscan_mode                     ),
    .capturedr  ( dft_bscan_capturedr                ),
    .shiftdr    ( dft_bscan_shiftdr                  ),          
    .updatedr   ( dft_bscan_updatedr                 ),               
    .pi         ( swi_int_gain_muxed_pre             ),               
    .po         ( int_gain_bscan_flop_po             ),               
    .tdi        ( {int_gain_tdo[3],
                   int_gain_tdo[2],
                   int_gain_tdo[1],
                   int_gain_tdo[0],
                   vco2_post_div_tdo[1]}     ),                
    .tdo        ( {int_gain_tdo[4],
                   int_gain_tdo[3],
                   int_gain_tdo[2],
                   int_gain_tdo[1],
                   int_gain_tdo[0]}     )); 

  assign swi_int_gain_muxed = int_gain_bscan_flop_po;

  //-----------------------
  //-----------------------

  wire [4:0]  swi_prop_gain_muxed_pre;
  wav_clock_mux u_wav_clock_mux_prop_gain[4:0] (
    .clk0    ( prop_gain                          ),              
    .clk1    ( reg_prop_gain                      ),              
    .sel     ( reg_prop_gain_mux                  ),      
    .clk_out ( swi_prop_gain_muxed_pre            )); 

  wire [4:0] prop_gain_tdo;


  wire [4:0] prop_gain_bscan_flop_po;
  mvp_pll_jtag_bsr u_mvp_pll_jtag_bsr_prop_gain[4:0] (   
    .tck        ( dft_bscan_tck                      ),          
    .trst_n     ( dft_bscan_trst_n                   ),      
    .bscan_mode ( dft_bscan_mode                     ),
    .capturedr  ( dft_bscan_capturedr                ),
    .shiftdr    ( dft_bscan_shiftdr                  ),          
    .updatedr   ( dft_bscan_updatedr                 ),               
    .pi         ( swi_prop_gain_muxed_pre            ),               
    .po         ( prop_gain_bscan_flop_po            ),               
    .tdi        ( {prop_gain_tdo[3],
                   prop_gain_tdo[2],
                   prop_gain_tdo[1],
                   prop_gain_tdo[0],
                   int_gain_tdo[4]}     ),                
    .tdo        ( {prop_gain_tdo[4],
                   prop_gain_tdo[3],
                   prop_gain_tdo[2],
                   prop_gain_tdo[1],
                   prop_gain_tdo[0]}     )); 

  assign swi_prop_gain_muxed = prop_gain_bscan_flop_po;

  //-----------------------




  //---------------------------
  // LOCK_DET_SETTINGS
  // ld_refclk_cycles - Number of refclk cycles to compare against fbclk for detecting lock. A higher number with tighter range equates to a lower PPM tolerance
  // ld_range - Range tolerance for refclk vs. fbclk during normal lock procedure
  //---------------------------
  wire [31:0] LOCK_DET_SETTINGS_reg_read;
  reg [15:0]  reg_ld_refclk_cycles;
  reg [5:0]   reg_ld_range;

  always @(posedge RegClk or posedge RegReset) begin
    if(RegReset) begin
      reg_ld_refclk_cycles                   <= 16'h200;
      reg_ld_range                           <= 6'h4;
    end else if(RegAddr == 'ha0 && RegWrEn) begin
      reg_ld_refclk_cycles                   <= RegWrData[15:0];
      reg_ld_range                           <= RegWrData[21:16];
    end else begin
      reg_ld_refclk_cycles                   <= reg_ld_refclk_cycles;
      reg_ld_range                           <= reg_ld_range;
    end
  end

  assign LOCK_DET_SETTINGS_reg_read = {10'h0,
          reg_ld_range,
          reg_ld_refclk_cycles};

  //-----------------------
  assign swi_ld_refclk_cycles = reg_ld_refclk_cycles;

  //-----------------------
  assign swi_ld_range = reg_ld_range;





  //---------------------------
  // FASTLOCK_DET_SETTINGS
  // fastld_refclk_cycles - Number of refclk cycles to compare against fbclk for detecting lock during fastlock. A higher number with tighter range equates to a lower PPM tolerance
  // fastld_range - Range tolerance for refclk vs. fbclk during fast lock procedure
  //---------------------------
  wire [31:0] FASTLOCK_DET_SETTINGS_reg_read;
  reg [15:0]  reg_fastld_refclk_cycles;
  reg [5:0]   reg_fastld_range;

  always @(posedge RegClk or posedge RegReset) begin
    if(RegReset) begin
      reg_fastld_refclk_cycles               <= 16'h100;
      reg_fastld_range                       <= 6'h8;
    end else if(RegAddr == 'ha4 && RegWrEn) begin
      reg_fastld_refclk_cycles               <= RegWrData[15:0];
      reg_fastld_range                       <= RegWrData[21:16];
    end else begin
      reg_fastld_refclk_cycles               <= reg_fastld_refclk_cycles;
      reg_fastld_range                       <= reg_fastld_range;
    end
  end

  assign FASTLOCK_DET_SETTINGS_reg_read = {10'h0,
          reg_fastld_range,
          reg_fastld_refclk_cycles};

  //-----------------------
  assign swi_fastld_refclk_cycles = reg_fastld_refclk_cycles;

  //-----------------------
  assign swi_fastld_range = reg_fastld_range;





  //---------------------------
  // ANALOG_EN_RESET
  // pll_en - PLL Enable override going to analog
  // pll_en_mux - 
  // pll_reset - PLL reset override going to analog
  // pll_reset_mux - 
  // fbdiv_sel - Feedback divider override going to analog
  // fbdiv_sel_mux - 
  // vco_sel - VCO Sel override going to analog
  // vco_sel_mux - 
  //---------------------------
  wire [31:0] ANALOG_EN_RESET_reg_read;
  reg          reg_pll_en;
  reg          reg_pll_reset;
  reg  [8:0]   reg_fbdiv_sel;
  reg  [1:0]   reg_vco_sel;

  always @(posedge RegClk or posedge RegReset) begin
    if(RegReset) begin
      reg_pll_en                             <= 1'h0;
      reg_pll_en_mux                         <= 1'h0;
      reg_pll_reset                          <= 1'h0;
      reg_pll_reset_mux                      <= 1'h0;
      reg_fbdiv_sel                          <= 9'h0;
      reg_fbdiv_sel_mux                      <= 1'h0;
      reg_vco_sel                            <= 2'h0;
      reg_vco_sel_mux                        <= 1'h0;
    end else if(RegAddr == 'ha8 && RegWrEn) begin
      reg_pll_en                             <= RegWrData[0];
      reg_pll_en_mux                         <= RegWrData[1];
      reg_pll_reset                          <= RegWrData[2];
      reg_pll_reset_mux                      <= RegWrData[3];
      reg_fbdiv_sel                          <= RegWrData[12:4];
      reg_fbdiv_sel_mux                      <= RegWrData[13];
      reg_vco_sel                            <= RegWrData[15:14];
      reg_vco_sel_mux                        <= RegWrData[16];
    end else begin
      reg_pll_en                             <= reg_pll_en;
      reg_pll_en_mux                         <= reg_pll_en_mux;
      reg_pll_reset                          <= reg_pll_reset;
      reg_pll_reset_mux                      <= reg_pll_reset_mux;
      reg_fbdiv_sel                          <= reg_fbdiv_sel;
      reg_fbdiv_sel_mux                      <= reg_fbdiv_sel_mux;
      reg_vco_sel                            <= reg_vco_sel;
      reg_vco_sel_mux                        <= reg_vco_sel_mux;
    end
  end

  assign ANALOG_EN_RESET_reg_read = {15'h0,
          reg_vco_sel_mux,
          reg_vco_sel,
          reg_fbdiv_sel_mux,
          reg_fbdiv_sel,
          reg_pll_reset_mux,
          reg_pll_reset,
          reg_pll_en_mux,
          reg_pll_en};

  //-----------------------

  wire        swi_pll_en_muxed_pre;
  wav_clock_mux u_wav_clock_mux_pll_en (
    .clk0    ( pll_en                             ),              
    .clk1    ( reg_pll_en                         ),              
    .sel     ( reg_pll_en_mux                     ),      
    .clk_out ( swi_pll_en_muxed_pre               )); 


  wire        reg_pll_en_core_scan_mode;
  wav_clock_mux u_wav_clock_mux_pll_en_core_scan_mode (
    .clk0    ( swi_pll_en_muxed_pre               ),              
    .clk1    ( 1'd0                               ),              
    .sel     ( dft_core_scan_mode                 ),      
    .clk_out ( reg_pll_en_core_scan_mode          )); 


  wire        reg_pll_en_iddq_mode;
  wav_clock_mux u_wav_clock_mux_pll_en_iddq_mode (
    .clk0    ( reg_pll_en_core_scan_mode          ),              
    .clk1    ( 1'd0                               ),              
    .sel     ( dft_iddq_mode                      ),      
    .clk_out ( reg_pll_en_iddq_mode               )); 

  wire  pll_en_tdo;


  wire  pll_en_bscan_flop_po;
  mvp_pll_jtag_bsr u_mvp_pll_jtag_bsr_pll_en (   
    .tck        ( dft_bscan_tck                      ),          
    .trst_n     ( dft_bscan_trst_n                   ),      
    .bscan_mode ( dft_bscan_mode                     ),
    .capturedr  ( dft_bscan_capturedr                ),
    .shiftdr    ( dft_bscan_shiftdr                  ),          
    .updatedr   ( dft_bscan_updatedr                 ),               
    .pi         ( reg_pll_en_iddq_mode               ),               
    .po         ( pll_en_bscan_flop_po               ),               
    .tdi        ( prop_gain_tdo[4]                   ),                
    .tdo        ( pll_en_tdo                         )); 

  assign swi_pll_en_muxed = pll_en_bscan_flop_po;

  //-----------------------
  //-----------------------

  wire        swi_pll_reset_muxed_pre;
  wav_clock_mux u_wav_clock_mux_pll_reset (
    .clk0    ( pll_reset                          ),              
    .clk1    ( reg_pll_reset                      ),              
    .sel     ( reg_pll_reset_mux                  ),      
    .clk_out ( swi_pll_reset_muxed_pre            )); 


  wire        reg_pll_reset_core_scan_mode;
  wav_clock_mux u_wav_clock_mux_pll_reset_core_scan_mode (
    .clk0    ( swi_pll_reset_muxed_pre            ),              
    .clk1    ( 1'd1                               ),              
    .sel     ( dft_core_scan_mode                 ),      
    .clk_out ( reg_pll_reset_core_scan_mode       )); 


  wire        reg_pll_reset_iddq_mode;
  wav_clock_mux u_wav_clock_mux_pll_reset_iddq_mode (
    .clk0    ( reg_pll_reset_core_scan_mode       ),              
    .clk1    ( 1'd1                               ),              
    .sel     ( dft_iddq_mode                      ),      
    .clk_out ( reg_pll_reset_iddq_mode            )); 

  wire  pll_reset_tdo;


  wire  pll_reset_bscan_flop_po;
  mvp_pll_jtag_bsr u_mvp_pll_jtag_bsr_pll_reset (   
    .tck        ( dft_bscan_tck                      ),          
    .trst_n     ( dft_bscan_trst_n                   ),      
    .bscan_mode ( dft_bscan_mode                     ),
    .capturedr  ( dft_bscan_capturedr                ),
    .shiftdr    ( dft_bscan_shiftdr                  ),          
    .updatedr   ( dft_bscan_updatedr                 ),               
    .pi         ( reg_pll_reset_iddq_mode            ),               
    .po         ( pll_reset_bscan_flop_po            ),               
    .tdi        ( pll_en_tdo                         ),                
    .tdo        ( pll_reset_tdo                      )); 

  assign swi_pll_reset_muxed = pll_reset_bscan_flop_po;

  //-----------------------
  //-----------------------

  wire [8:0]  swi_fbdiv_sel_muxed_pre;
  wav_clock_mux u_wav_clock_mux_fbdiv_sel[8:0] (
    .clk0    ( fbdiv_sel                          ),              
    .clk1    ( reg_fbdiv_sel                      ),              
    .sel     ( reg_fbdiv_sel_mux                  ),      
    .clk_out ( swi_fbdiv_sel_muxed_pre            )); 

  wire [8:0] fbdiv_sel_tdo;


  wire [8:0] fbdiv_sel_bscan_flop_po;
  mvp_pll_jtag_bsr u_mvp_pll_jtag_bsr_fbdiv_sel[8:0] (   
    .tck        ( dft_bscan_tck                      ),          
    .trst_n     ( dft_bscan_trst_n                   ),      
    .bscan_mode ( dft_bscan_mode                     ),
    .capturedr  ( dft_bscan_capturedr                ),
    .shiftdr    ( dft_bscan_shiftdr                  ),          
    .updatedr   ( dft_bscan_updatedr                 ),               
    .pi         ( swi_fbdiv_sel_muxed_pre            ),               
    .po         ( fbdiv_sel_bscan_flop_po            ),               
    .tdi        ( {fbdiv_sel_tdo[7],
                   fbdiv_sel_tdo[6],
                   fbdiv_sel_tdo[5],
                   fbdiv_sel_tdo[4],
                   fbdiv_sel_tdo[3],
                   fbdiv_sel_tdo[2],
                   fbdiv_sel_tdo[1],
                   fbdiv_sel_tdo[0],
                   pll_reset_tdo}     ),                
    .tdo        ( {fbdiv_sel_tdo[8],
                   fbdiv_sel_tdo[7],
                   fbdiv_sel_tdo[6],
                   fbdiv_sel_tdo[5],
                   fbdiv_sel_tdo[4],
                   fbdiv_sel_tdo[3],
                   fbdiv_sel_tdo[2],
                   fbdiv_sel_tdo[1],
                   fbdiv_sel_tdo[0]}     )); 

  assign swi_fbdiv_sel_muxed = fbdiv_sel_bscan_flop_po;

  //-----------------------
  //-----------------------

  wire [1:0]  swi_vco_sel_muxed_pre;
  wav_clock_mux u_wav_clock_mux_vco_sel[1:0] (
    .clk0    ( vco_sel                            ),              
    .clk1    ( reg_vco_sel                        ),              
    .sel     ( reg_vco_sel_mux                    ),      
    .clk_out ( swi_vco_sel_muxed_pre              )); 

  wire [1:0] vco_sel_tdo;


  wire [1:0] vco_sel_bscan_flop_po;
  mvp_pll_jtag_bsr u_mvp_pll_jtag_bsr_vco_sel[1:0] (   
    .tck        ( dft_bscan_tck                      ),          
    .trst_n     ( dft_bscan_trst_n                   ),      
    .bscan_mode ( dft_bscan_mode                     ),
    .capturedr  ( dft_bscan_capturedr                ),
    .shiftdr    ( dft_bscan_shiftdr                  ),          
    .updatedr   ( dft_bscan_updatedr                 ),               
    .pi         ( swi_vco_sel_muxed_pre              ),               
    .po         ( vco_sel_bscan_flop_po              ),               
    .tdi        ( {vco_sel_tdo[0],
                   fbdiv_sel_tdo[8]}     ),                
    .tdo        ( {vco_sel_tdo[1],
                   vco_sel_tdo[0]}     )); 

  assign swi_vco_sel_muxed = vco_sel_bscan_flop_po;

  //-----------------------




  //---------------------------
  // MODE_DTST_MISC
  // bias_lvl - Bias Level analog control
  // cp_int_mode - Analog control, keep at 0x0
  // en_lock_det - Override for enabling lock detect. Should only be used in testing.
  // en_lock_det_mux - 1 - Use value from register. 0 - Hardware controlled
  // div16en - Enables div16 from VCO post dividers
  // bias_sel - 0 - Internal Bias
  //---------------------------
  wire [31:0] MODE_DTST_MISC_reg_read;
  reg [3:0]   reg_bias_lvl;
  reg         reg_cp_int_mode;
  reg          reg_en_lock_det;
  reg         reg_div16en;
  reg         reg_bias_sel;

  always @(posedge RegClk or posedge RegReset) begin
    if(RegReset) begin
      reg_bias_lvl                           <= 4'h8;
      reg_cp_int_mode                        <= 1'h0;
      reg_en_lock_det                        <= 1'h0;
      reg_en_lock_det_mux                    <= 1'h0;
      reg_div16en                            <= 1'h0;
      reg_bias_sel                           <= 1'h0;
    end else if(RegAddr == 'hac && RegWrEn) begin
      reg_bias_lvl                           <= RegWrData[3:0];
      reg_cp_int_mode                        <= RegWrData[4];
      reg_en_lock_det                        <= RegWrData[5];
      reg_en_lock_det_mux                    <= RegWrData[6];
      reg_div16en                            <= RegWrData[7];
      reg_bias_sel                           <= RegWrData[8];
    end else begin
      reg_bias_lvl                           <= reg_bias_lvl;
      reg_cp_int_mode                        <= reg_cp_int_mode;
      reg_en_lock_det                        <= reg_en_lock_det;
      reg_en_lock_det_mux                    <= reg_en_lock_det_mux;
      reg_div16en                            <= reg_div16en;
      reg_bias_sel                           <= reg_bias_sel;
    end
  end

  assign MODE_DTST_MISC_reg_read = {23'h0,
          reg_bias_sel,
          reg_div16en,
          reg_en_lock_det_mux,
          reg_en_lock_det,
          reg_cp_int_mode,
          reg_bias_lvl};

  //-----------------------
  wire [3:0] bias_lvl_tdo;


  wire [3:0] bias_lvl_bscan_flop_po;
  mvp_pll_jtag_bsr u_mvp_pll_jtag_bsr_bias_lvl[3:0] (   
    .tck        ( dft_bscan_tck                      ),          
    .trst_n     ( dft_bscan_trst_n                   ),      
    .bscan_mode ( dft_bscan_mode                     ),
    .capturedr  ( dft_bscan_capturedr                ),
    .shiftdr    ( dft_bscan_shiftdr                  ),          
    .updatedr   ( dft_bscan_updatedr                 ),               
    .pi         ( reg_bias_lvl                       ),               
    .po         ( bias_lvl_bscan_flop_po             ),               
    .tdi        ( {bias_lvl_tdo[2],
                   bias_lvl_tdo[1],
                   bias_lvl_tdo[0],
                   vco_sel_tdo[1]}     ),                
    .tdo        ( {bias_lvl_tdo[3],
                   bias_lvl_tdo[2],
                   bias_lvl_tdo[1],
                   bias_lvl_tdo[0]}     )); 

  assign swi_bias_lvl = bias_lvl_bscan_flop_po;

  //-----------------------

  wire        reg_cp_int_mode_core_scan_mode;
  wav_clock_mux u_wav_clock_mux_cp_int_mode_core_scan_mode (
    .clk0    ( reg_cp_int_mode                    ),              
    .clk1    ( 1'd0                               ),              
    .sel     ( dft_core_scan_mode                 ),      
    .clk_out ( reg_cp_int_mode_core_scan_mode     )); 


  wire        reg_cp_int_mode_iddq_mode;
  wav_clock_mux u_wav_clock_mux_cp_int_mode_iddq_mode (
    .clk0    ( reg_cp_int_mode_core_scan_mode     ),              
    .clk1    ( 1'd0                               ),              
    .sel     ( dft_iddq_mode                      ),      
    .clk_out ( reg_cp_int_mode_iddq_mode          )); 


  wire        reg_cp_int_mode_bscan_mode;
  wav_clock_mux u_wav_clock_mux_cp_int_mode_bscan_mode (
    .clk0    ( reg_cp_int_mode_iddq_mode          ),              
    .clk1    ( 1'd0                               ),              
    .sel     ( dft_bscan_mode                     ),      
    .clk_out ( reg_cp_int_mode_bscan_mode         )); 

  assign swi_cp_int_mode = reg_cp_int_mode_bscan_mode;

  //-----------------------

  wire        swi_en_lock_det_muxed_pre;
  wav_clock_mux u_wav_clock_mux_en_lock_det (
    .clk0    ( en_lock_det                        ),              
    .clk1    ( reg_en_lock_det                    ),              
    .sel     ( reg_en_lock_det_mux                ),      
    .clk_out ( swi_en_lock_det_muxed_pre          )); 

  assign swi_en_lock_det_muxed = swi_en_lock_det_muxed_pre;

  //-----------------------
  //-----------------------
  wire  div16en_tdo;


  wire  div16en_bscan_flop_po;
  mvp_pll_jtag_bsr u_mvp_pll_jtag_bsr_div16en (   
    .tck        ( dft_bscan_tck                      ),          
    .trst_n     ( dft_bscan_trst_n                   ),      
    .bscan_mode ( dft_bscan_mode                     ),
    .capturedr  ( dft_bscan_capturedr                ),
    .shiftdr    ( dft_bscan_shiftdr                  ),          
    .updatedr   ( dft_bscan_updatedr                 ),               
    .pi         ( reg_div16en                        ),               
    .po         ( div16en_bscan_flop_po              ),               
    .tdi        ( bias_lvl_tdo[3]                    ),                
    .tdo        ( div16en_tdo                        )); 

  assign swi_div16en = div16en_bscan_flop_po;

  //-----------------------
  wire  bias_sel_tdo;


  wire  bias_sel_bscan_flop_po;
  mvp_pll_jtag_bsr u_mvp_pll_jtag_bsr_bias_sel (   
    .tck        ( dft_bscan_tck                      ),          
    .trst_n     ( dft_bscan_trst_n                   ),      
    .bscan_mode ( dft_bscan_mode                     ),
    .capturedr  ( dft_bscan_capturedr                ),
    .shiftdr    ( dft_bscan_shiftdr                  ),          
    .updatedr   ( dft_bscan_updatedr                 ),               
    .pi         ( reg_bias_sel                       ),               
    .po         ( bias_sel_bscan_flop_po             ),               
    .tdi        ( div16en_tdo                        ),                
    .tdo        ( bias_sel_tdo                       )); 

  assign swi_bias_sel = bias_sel_bscan_flop_po;





  //---------------------------
  // PROP_CTRLS
  // prop_c_ctrl - 
  // prop_r_ctrl - 
  //---------------------------
  wire [31:0] PROP_CTRLS_reg_read;
  reg [1:0]   reg_prop_c_ctrl;
  reg [1:0]   reg_prop_r_ctrl;

  always @(posedge RegClk or posedge RegReset) begin
    if(RegReset) begin
      reg_prop_c_ctrl                        <= 2'h0;
      reg_prop_r_ctrl                        <= 2'h0;
    end else if(RegAddr == 'hb0 && RegWrEn) begin
      reg_prop_c_ctrl                        <= RegWrData[1:0];
      reg_prop_r_ctrl                        <= RegWrData[3:2];
    end else begin
      reg_prop_c_ctrl                        <= reg_prop_c_ctrl;
      reg_prop_r_ctrl                        <= reg_prop_r_ctrl;
    end
  end

  assign PROP_CTRLS_reg_read = {28'h0,
          reg_prop_r_ctrl,
          reg_prop_c_ctrl};

  //-----------------------
  wire [1:0] prop_c_ctrl_tdo;


  wire [1:0] prop_c_ctrl_bscan_flop_po;
  mvp_pll_jtag_bsr u_mvp_pll_jtag_bsr_prop_c_ctrl[1:0] (   
    .tck        ( dft_bscan_tck                      ),          
    .trst_n     ( dft_bscan_trst_n                   ),      
    .bscan_mode ( dft_bscan_mode                     ),
    .capturedr  ( dft_bscan_capturedr                ),
    .shiftdr    ( dft_bscan_shiftdr                  ),          
    .updatedr   ( dft_bscan_updatedr                 ),               
    .pi         ( reg_prop_c_ctrl                    ),               
    .po         ( prop_c_ctrl_bscan_flop_po          ),               
    .tdi        ( {prop_c_ctrl_tdo[0],
                   bias_sel_tdo}     ),                
    .tdo        ( {prop_c_ctrl_tdo[1],
                   prop_c_ctrl_tdo[0]}     )); 

  assign swi_prop_c_ctrl = prop_c_ctrl_bscan_flop_po;

  //-----------------------
  wire [1:0] prop_r_ctrl_tdo;


  wire [1:0] prop_r_ctrl_bscan_flop_po;
  mvp_pll_jtag_bsr u_mvp_pll_jtag_bsr_prop_r_ctrl[1:0] (   
    .tck        ( dft_bscan_tck                      ),          
    .trst_n     ( dft_bscan_trst_n                   ),      
    .bscan_mode ( dft_bscan_mode                     ),
    .capturedr  ( dft_bscan_capturedr                ),
    .shiftdr    ( dft_bscan_shiftdr                  ),          
    .updatedr   ( dft_bscan_updatedr                 ),               
    .pi         ( reg_prop_r_ctrl                    ),               
    .po         ( prop_r_ctrl_bscan_flop_po          ),               
    .tdi        ( {prop_r_ctrl_tdo[0],
                   prop_c_ctrl_tdo[1]}     ),                
    .tdo        ( {prop_r_ctrl_tdo[1],
                   prop_r_ctrl_tdo[0]}     )); 

  assign swi_prop_r_ctrl = prop_r_ctrl_bscan_flop_po;





  //---------------------------
  // REFCLK_CONTROLS
  // pfd_mode - 
  // sel_refclk_alt - 
  //---------------------------
  wire [31:0] REFCLK_CONTROLS_reg_read;
  reg [1:0]   reg_pfd_mode;
  reg         reg_sel_refclk_alt;

  always @(posedge RegClk or posedge RegReset) begin
    if(RegReset) begin
      reg_pfd_mode                           <= 2'h0;
      reg_sel_refclk_alt                     <= 1'h0;
    end else if(RegAddr == 'hb4 && RegWrEn) begin
      reg_pfd_mode                           <= RegWrData[1:0];
      reg_sel_refclk_alt                     <= RegWrData[2];
    end else begin
      reg_pfd_mode                           <= reg_pfd_mode;
      reg_sel_refclk_alt                     <= reg_sel_refclk_alt;
    end
  end

  assign REFCLK_CONTROLS_reg_read = {29'h0,
          reg_sel_refclk_alt,
          reg_pfd_mode};

  //-----------------------
  wire [1:0] pfd_mode_tdo;


  wire [1:0] pfd_mode_bscan_flop_po;
  mvp_pll_jtag_bsr u_mvp_pll_jtag_bsr_pfd_mode[1:0] (   
    .tck        ( dft_bscan_tck                      ),          
    .trst_n     ( dft_bscan_trst_n                   ),      
    .bscan_mode ( dft_bscan_mode                     ),
    .capturedr  ( dft_bscan_capturedr                ),
    .shiftdr    ( dft_bscan_shiftdr                  ),          
    .updatedr   ( dft_bscan_updatedr                 ),               
    .pi         ( reg_pfd_mode                       ),               
    .po         ( pfd_mode_bscan_flop_po             ),               
    .tdi        ( {pfd_mode_tdo[0],
                   prop_r_ctrl_tdo[1]}     ),                
    .tdo        ( {pfd_mode_tdo[1],
                   pfd_mode_tdo[0]}     )); 

  assign swi_pfd_mode = pfd_mode_bscan_flop_po;

  //-----------------------
  wire  sel_refclk_alt_tdo;


  wire  sel_refclk_alt_bscan_flop_po;
  mvp_pll_jtag_bsr u_mvp_pll_jtag_bsr_sel_refclk_alt (   
    .tck        ( dft_bscan_tck                      ),          
    .trst_n     ( dft_bscan_trst_n                   ),      
    .bscan_mode ( dft_bscan_mode                     ),
    .capturedr  ( dft_bscan_capturedr                ),
    .shiftdr    ( dft_bscan_shiftdr                  ),          
    .updatedr   ( dft_bscan_updatedr                 ),               
    .pi         ( reg_sel_refclk_alt                 ),               
    .po         ( sel_refclk_alt_bscan_flop_po       ),               
    .tdi        ( pfd_mode_tdo[1]                    ),                
    .tdo        ( sel_refclk_alt_tdo                 )); 

  assign swi_sel_refclk_alt = sel_refclk_alt_bscan_flop_po;





  //---------------------------
  // CLKGATE_DISABLES
  // force_fbclk_gate - 1 - Disables clock gating for digital. 0 - Uses hardware control
  // force_vco0_clk_gate - 1 - Disables clock gating for digital. 0 - Uses hardware control
  // force_vco1_clk_gate - 1 - Disables clock gating for digital. 0 - Uses hardware control
  // force_vco2_clk_gate - 1 - Disables clock gating for digital. 0 - Uses hardware control
  //---------------------------
  wire [31:0] CLKGATE_DISABLES_reg_read;
  reg         reg_force_fbclk_gate;
  reg         reg_force_vco0_clk_gate;
  reg         reg_force_vco1_clk_gate;
  reg         reg_force_vco2_clk_gate;

  always @(posedge RegClk or posedge RegReset) begin
    if(RegReset) begin
      reg_force_fbclk_gate                   <= 1'h0;
      reg_force_vco0_clk_gate                <= 1'h0;
      reg_force_vco1_clk_gate                <= 1'h0;
      reg_force_vco2_clk_gate                <= 1'h0;
    end else if(RegAddr == 'hb8 && RegWrEn) begin
      reg_force_fbclk_gate                   <= RegWrData[0];
      reg_force_vco0_clk_gate                <= RegWrData[1];
      reg_force_vco1_clk_gate                <= RegWrData[2];
      reg_force_vco2_clk_gate                <= RegWrData[3];
    end else begin
      reg_force_fbclk_gate                   <= reg_force_fbclk_gate;
      reg_force_vco0_clk_gate                <= reg_force_vco0_clk_gate;
      reg_force_vco1_clk_gate                <= reg_force_vco1_clk_gate;
      reg_force_vco2_clk_gate                <= reg_force_vco2_clk_gate;
    end
  end

  assign CLKGATE_DISABLES_reg_read = {28'h0,
          reg_force_vco2_clk_gate,
          reg_force_vco1_clk_gate,
          reg_force_vco0_clk_gate,
          reg_force_fbclk_gate};

  //-----------------------
  assign swi_force_fbclk_gate = reg_force_fbclk_gate;

  //-----------------------
  assign swi_force_vco0_clk_gate = reg_force_vco0_clk_gate;

  //-----------------------
  assign swi_force_vco1_clk_gate = reg_force_vco1_clk_gate;

  //-----------------------
  assign swi_force_vco2_clk_gate = reg_force_vco2_clk_gate;





  //---------------------------
  // DEBUG_BUS_CTRL
  // DEBUG_BUS_CTRL_SEL - Select signal for DEBUG_BUS_CTRL
  //---------------------------
  wire [31:0] DEBUG_BUS_CTRL_reg_read;
  reg [5:0]   reg_debug_bus_ctrl_sel;
  wire [5:0]   swi_debug_bus_ctrl_sel;

  always @(posedge RegClk or posedge RegReset) begin
    if(RegReset) begin
      reg_debug_bus_ctrl_sel                 <= 6'h0;
    end else if(RegAddr == 'hbc && RegWrEn) begin
      reg_debug_bus_ctrl_sel                 <= RegWrData[5:0];
    end else begin
      reg_debug_bus_ctrl_sel                 <= reg_debug_bus_ctrl_sel;
    end
  end

  assign DEBUG_BUS_CTRL_reg_read = {26'h0,
          reg_debug_bus_ctrl_sel};

  //-----------------------
  assign swi_debug_bus_ctrl_sel = reg_debug_bus_ctrl_sel;





  //---------------------------
  // DEBUG_BUS_STATUS
  // DEBUG_BUS_CTRL_STATUS - Status output for DEBUG_BUS_STATUS
  //---------------------------
  wire [31:0] DEBUG_BUS_STATUS_reg_read;

  //Debug bus control logic  
  always @(*) begin
    case(swi_debug_bus_ctrl_sel)
      'd0 : debug_bus_ctrl_status = {7'd0, fsm_state, freq_detect_cycles, freq_detect_lock, core_initial_switch_done, core_fastlock_ready, core_ready};
      'd1 : debug_bus_ctrl_status = {3'd0, vco0_locked, vco0_too_slow_status, vco0_too_fast_status, 1'd0, 1'd0, 1'd0, 4'd0, 1'd0, 4'd0, 6'd0, 6'd0, 1'd0, 1'd0};
      'd2 : debug_bus_ctrl_status = {8'd0, vco0_fine_prev_status, vco0_fine_status, vco0_band_prev_status, vco0_band_status};
      'd3 : debug_bus_ctrl_status = {16'd0, vco0_vco_count};
      'd4 : debug_bus_ctrl_status = {3'd0, vco1_locked, vco1_too_slow_status, vco1_too_fast_status, 1'd0, 1'd0, 1'd0, 4'd0, 1'd0, 4'd0, 6'd0, 6'd0, 1'd0, 1'd0};
      'd5 : debug_bus_ctrl_status = {8'd0, vco1_fine_prev_status, vco1_fine_status, vco1_band_prev_status, vco1_band_status};
      'd6 : debug_bus_ctrl_status = {16'd0, vco1_vco_count};
      'd7 : debug_bus_ctrl_status = {3'd0, vco2_locked, vco2_too_slow_status, vco2_too_fast_status, 1'd0, 1'd0, 1'd0, 4'd0, 1'd0, 4'd0, 6'd0, 6'd0, 1'd0, 1'd0};
      'd8 : debug_bus_ctrl_status = {8'd0, vco2_fine_prev_status, vco2_fine_status, vco2_band_prev_status, vco2_band_status};
      'd9 : debug_bus_ctrl_status = {16'd0, vco2_vco_count};
      'd10 : debug_bus_ctrl_status = {31'd0, swi_core_reset_muxed};
      'd11 : debug_bus_ctrl_status = {30'd0, swi_core_vco_sel_muxed};
      'd12 : debug_bus_ctrl_status = {31'd0, swi_core_gfcm_sel_muxed};
      'd13 : debug_bus_ctrl_status = {31'd0, swi_core_switch_vco_hw_muxed};
      'd14 : debug_bus_ctrl_status = {26'd0, swi_vco0_band_muxed};
      'd15 : debug_bus_ctrl_status = {26'd0, swi_vco0_fine_muxed};
      'd16 : debug_bus_ctrl_status = {31'd0, swi_vco0_ena_muxed};
      'd17 : debug_bus_ctrl_status = {26'd0, swi_vco1_band_muxed};
      'd18 : debug_bus_ctrl_status = {26'd0, swi_vco1_fine_muxed};
      'd19 : debug_bus_ctrl_status = {31'd0, swi_vco1_ena_muxed};
      'd20 : debug_bus_ctrl_status = {26'd0, swi_vco2_band_muxed};
      'd21 : debug_bus_ctrl_status = {26'd0, swi_vco2_fine_muxed};
      'd22 : debug_bus_ctrl_status = {31'd0, swi_vco2_ena_muxed};
      'd23 : debug_bus_ctrl_status = {27'd0, swi_int_gain_muxed};
      'd24 : debug_bus_ctrl_status = {27'd0, swi_prop_gain_muxed};
      'd25 : debug_bus_ctrl_status = {31'd0, swi_pll_en_muxed};
      'd26 : debug_bus_ctrl_status = {31'd0, swi_pll_reset_muxed};
      'd27 : debug_bus_ctrl_status = {23'd0, swi_fbdiv_sel_muxed};
      'd28 : debug_bus_ctrl_status = {30'd0, swi_vco_sel_muxed};
      'd29 : debug_bus_ctrl_status = {31'd0, swi_en_lock_det_muxed};
      default : debug_bus_ctrl_status = 32'd0;
    endcase
  end 
  
  assign DEBUG_BUS_STATUS_reg_read = {          debug_bus_ctrl_status};

  //-----------------------

  //=======================
  // Final BSCAN Connection
  //=======================
  assign dft_bscan_tdo = sel_refclk_alt_tdo;


  
    
  //---------------------------
  // PRDATA Selection
  //---------------------------
  reg [31:0] prdata_sel;
  
  always @(*) begin
    if(RegRdEn) begin
      case(RegAddr)
       'h0    : prdata_sel = CORE_OVERRIDES_reg_read;
       'h4    : prdata_sel = CORE_SWTICH_VCO_reg_read;
       'h8    : prdata_sel = CORE_SWTICH_VCO_HW_reg_read;
       'hc    : prdata_sel = CORE_STATUS_reg_read;
       'h10   : prdata_sel = CORE_STATUS_INT_reg_read;
       'h14   : prdata_sel = CORE_STATUS_INT_EN_reg_read;
       'h18   : prdata_sel = VCO0_BAND_reg_read;
       'h1c   : prdata_sel = VCO0_CONTROL_reg_read;
       'h20   : prdata_sel = VCO0_FLL_CONTROL1_reg_read;
       'h24   : prdata_sel = VCO0_FLL_CONTROL2_reg_read;
       'h28   : prdata_sel = VCO0_FLL_CONTROL3_reg_read;
       'h2c   : prdata_sel = VCO0_FLL_BAND_STATUS_reg_read;
       'h30   : prdata_sel = VCO0_FLL_COUNT_STATUS_reg_read;
       'h34   : prdata_sel = VCO0_INT_FRAC_SETTINGS_reg_read;
       'h38   : prdata_sel = VCO0_PROP_GAINS_reg_read;
       'h3c   : prdata_sel = VCO1_BAND_reg_read;
       'h40   : prdata_sel = VCO1_CONTROL_reg_read;
       'h44   : prdata_sel = VCO1_FLL_CONTROL1_reg_read;
       'h48   : prdata_sel = VCO1_FLL_CONTROL2_reg_read;
       'h4c   : prdata_sel = VCO1_FLL_CONTROL3_reg_read;
       'h50   : prdata_sel = VCO1_FLL_BAND_STATUS_reg_read;
       'h54   : prdata_sel = VCO1_FLL_COUNT_STATUS_reg_read;
       'h58   : prdata_sel = VCO1_INT_FRAC_SETTINGS_reg_read;
       'h5c   : prdata_sel = VCO1_PROP_GAINS_reg_read;
       'h60   : prdata_sel = VCO1_SSC_CONTROLS_reg_read;
       'h64   : prdata_sel = VCO2_BAND_reg_read;
       'h68   : prdata_sel = VCO2_CONTROL_reg_read;
       'h6c   : prdata_sel = VCO2_FLL_CONTROL1_reg_read;
       'h70   : prdata_sel = VCO2_FLL_CONTROL2_reg_read;
       'h74   : prdata_sel = VCO2_FLL_CONTROL3_reg_read;
       'h78   : prdata_sel = VCO2_FLL_BAND_STATUS_reg_read;
       'h7c   : prdata_sel = VCO2_FLL_COUNT_STATUS_reg_read;
       'h80   : prdata_sel = VCO2_INT_FRAC_SETTINGS_reg_read;
       'h84   : prdata_sel = VCO2_PROP_GAINS_reg_read;
       'h88   : prdata_sel = VCO2_SSC_CONTROLS_reg_read;
       'h8c   : prdata_sel = STATE_MACHINE_CONTROLS_reg_read;
       'h90   : prdata_sel = STATE_MACHINE_CONTROLS2_reg_read;
       'h94   : prdata_sel = INTR_GAINS_reg_read;
       'h98   : prdata_sel = INTR_PROP_FL_GAINS_reg_read;
       'h9c   : prdata_sel = INTR_PROP_GAINS_OVERRIDE_reg_read;
       'ha0   : prdata_sel = LOCK_DET_SETTINGS_reg_read;
       'ha4   : prdata_sel = FASTLOCK_DET_SETTINGS_reg_read;
       'ha8   : prdata_sel = ANALOG_EN_RESET_reg_read;
       'hac   : prdata_sel = MODE_DTST_MISC_reg_read;
       'hb0   : prdata_sel = PROP_CTRLS_reg_read;
       'hb4   : prdata_sel = REFCLK_CONTROLS_reg_read;
       'hb8   : prdata_sel = CLKGATE_DISABLES_reg_read;
       'hbc   : prdata_sel = DEBUG_BUS_CTRL_reg_read;
       'hc0   : prdata_sel = DEBUG_BUS_STATUS_reg_read;

        default : prdata_sel = 32'd0;
      endcase
    end else begin
      prdata_sel = 32'd0;
    end
  end
    
  
  assign hrdata = prdata_sel;


  
    
  //---------------------------
  // PSLVERR Detection
  //---------------------------
  reg pslverr_pre;
  
  always @(*) begin
    if(RegWrEn || RegRdEn) begin
      case(RegAddr)
       'h0    : pslverr_pre = 1'b0;
       'h4    : pslverr_pre = 1'b0;
       'h8    : pslverr_pre = 1'b0;
       'hc    : pslverr_pre = 1'b0;
       'h10   : pslverr_pre = 1'b0;
       'h14   : pslverr_pre = 1'b0;
       'h18   : pslverr_pre = 1'b0;
       'h1c   : pslverr_pre = 1'b0;
       'h20   : pslverr_pre = 1'b0;
       'h24   : pslverr_pre = 1'b0;
       'h28   : pslverr_pre = 1'b0;
       'h2c   : pslverr_pre = 1'b0;
       'h30   : pslverr_pre = 1'b0;
       'h34   : pslverr_pre = 1'b0;
       'h38   : pslverr_pre = 1'b0;
       'h3c   : pslverr_pre = 1'b0;
       'h40   : pslverr_pre = 1'b0;
       'h44   : pslverr_pre = 1'b0;
       'h48   : pslverr_pre = 1'b0;
       'h4c   : pslverr_pre = 1'b0;
       'h50   : pslverr_pre = 1'b0;
       'h54   : pslverr_pre = 1'b0;
       'h58   : pslverr_pre = 1'b0;
       'h5c   : pslverr_pre = 1'b0;
       'h60   : pslverr_pre = 1'b0;
       'h64   : pslverr_pre = 1'b0;
       'h68   : pslverr_pre = 1'b0;
       'h6c   : pslverr_pre = 1'b0;
       'h70   : pslverr_pre = 1'b0;
       'h74   : pslverr_pre = 1'b0;
       'h78   : pslverr_pre = 1'b0;
       'h7c   : pslverr_pre = 1'b0;
       'h80   : pslverr_pre = 1'b0;
       'h84   : pslverr_pre = 1'b0;
       'h88   : pslverr_pre = 1'b0;
       'h8c   : pslverr_pre = 1'b0;
       'h90   : pslverr_pre = 1'b0;
       'h94   : pslverr_pre = 1'b0;
       'h98   : pslverr_pre = 1'b0;
       'h9c   : pslverr_pre = 1'b0;
       'ha0   : pslverr_pre = 1'b0;
       'ha4   : pslverr_pre = 1'b0;
       'ha8   : pslverr_pre = 1'b0;
       'hac   : pslverr_pre = 1'b0;
       'hb0   : pslverr_pre = 1'b0;
       'hb4   : pslverr_pre = 1'b0;
       'hb8   : pslverr_pre = 1'b0;
       'hbc   : pslverr_pre = 1'b0;
       'hc0   : pslverr_pre = 1'b0;

        default : pslverr_pre = 1'b1;
      endcase
    end else begin
      pslverr_pre = 1'b0;
    end
  end
  
  assign hresp = pslverr_pre ? 2'b01 : 2'b00;


  `ifdef SIMULATION
  
  reg [8*200:1] file_name;
  integer       file;
  initial begin
    if ($value$plusargs("MVP_PLL_BSR_MONITOR=%s", file_name)) begin
      file = $fopen(file_name, "w");
      $display("Starting MVP_PLL_BSR_MONITOR with file: %s", file_name);
      forever begin
        @(posedge RegClk);
        if(RegWrEn) begin
          @(posedge RegClk);  //Wait 1 clock cycle for update
          $fwrite(file, "#Update @ %t\n", $realtime);
          $fwrite(file, "%1b // jtag_chain0 vco0_band[0]\n", reg_vco0_band[0]);
          $fwrite(file, "%1b // jtag_chain1 vco0_band[1]\n", reg_vco0_band[1]);
          $fwrite(file, "%1b // jtag_chain2 vco0_band[2]\n", reg_vco0_band[2]);
          $fwrite(file, "%1b // jtag_chain3 vco0_band[3]\n", reg_vco0_band[3]);
          $fwrite(file, "%1b // jtag_chain4 vco0_band[4]\n", reg_vco0_band[4]);
          $fwrite(file, "%1b // jtag_chain5 vco0_band[5]\n", reg_vco0_band[5]);
          $fwrite(file, "%1b // jtag_chain6 vco0_fine[0]\n", reg_vco0_fine[0]);
          $fwrite(file, "%1b // jtag_chain7 vco0_fine[1]\n", reg_vco0_fine[1]);
          $fwrite(file, "%1b // jtag_chain8 vco0_fine[2]\n", reg_vco0_fine[2]);
          $fwrite(file, "%1b // jtag_chain9 vco0_fine[3]\n", reg_vco0_fine[3]);
          $fwrite(file, "%1b // jtag_chain10 vco0_fine[4]\n", reg_vco0_fine[4]);
          $fwrite(file, "%1b // jtag_chain11 vco0_fine[5]\n", reg_vco0_fine[5]);
          $fwrite(file, "%1b // jtag_chain12 vco0_ena\n", reg_vco0_ena);
          $fwrite(file, "%1b // jtag_chain13 vco0_byp_clk_sel\n", reg_vco0_byp_clk_sel);
          $fwrite(file, "%1b // jtag_chain14 vco1_band[0]\n", reg_vco1_band[0]);
          $fwrite(file, "%1b // jtag_chain15 vco1_band[1]\n", reg_vco1_band[1]);
          $fwrite(file, "%1b // jtag_chain16 vco1_band[2]\n", reg_vco1_band[2]);
          $fwrite(file, "%1b // jtag_chain17 vco1_band[3]\n", reg_vco1_band[3]);
          $fwrite(file, "%1b // jtag_chain18 vco1_band[4]\n", reg_vco1_band[4]);
          $fwrite(file, "%1b // jtag_chain19 vco1_band[5]\n", reg_vco1_band[5]);
          $fwrite(file, "%1b // jtag_chain20 vco1_fine[0]\n", reg_vco1_fine[0]);
          $fwrite(file, "%1b // jtag_chain21 vco1_fine[1]\n", reg_vco1_fine[1]);
          $fwrite(file, "%1b // jtag_chain22 vco1_fine[2]\n", reg_vco1_fine[2]);
          $fwrite(file, "%1b // jtag_chain23 vco1_fine[3]\n", reg_vco1_fine[3]);
          $fwrite(file, "%1b // jtag_chain24 vco1_fine[4]\n", reg_vco1_fine[4]);
          $fwrite(file, "%1b // jtag_chain25 vco1_fine[5]\n", reg_vco1_fine[5]);
          $fwrite(file, "%1b // jtag_chain26 vco1_ena\n", reg_vco1_ena);
          $fwrite(file, "%1b // jtag_chain27 vco1_byp_clk_sel\n", reg_vco1_byp_clk_sel);
          $fwrite(file, "%1b // jtag_chain28 vco1_post_div[0]\n", reg_vco1_post_div[0]);
          $fwrite(file, "%1b // jtag_chain29 vco1_post_div[1]\n", reg_vco1_post_div[1]);
          $fwrite(file, "%1b // jtag_chain30 vco2_band[0]\n", reg_vco2_band[0]);
          $fwrite(file, "%1b // jtag_chain31 vco2_band[1]\n", reg_vco2_band[1]);
          $fwrite(file, "%1b // jtag_chain32 vco2_band[2]\n", reg_vco2_band[2]);
          $fwrite(file, "%1b // jtag_chain33 vco2_band[3]\n", reg_vco2_band[3]);
          $fwrite(file, "%1b // jtag_chain34 vco2_band[4]\n", reg_vco2_band[4]);
          $fwrite(file, "%1b // jtag_chain35 vco2_band[5]\n", reg_vco2_band[5]);
          $fwrite(file, "%1b // jtag_chain36 vco2_fine[0]\n", reg_vco2_fine[0]);
          $fwrite(file, "%1b // jtag_chain37 vco2_fine[1]\n", reg_vco2_fine[1]);
          $fwrite(file, "%1b // jtag_chain38 vco2_fine[2]\n", reg_vco2_fine[2]);
          $fwrite(file, "%1b // jtag_chain39 vco2_fine[3]\n", reg_vco2_fine[3]);
          $fwrite(file, "%1b // jtag_chain40 vco2_fine[4]\n", reg_vco2_fine[4]);
          $fwrite(file, "%1b // jtag_chain41 vco2_fine[5]\n", reg_vco2_fine[5]);
          $fwrite(file, "%1b // jtag_chain42 vco2_ena\n", reg_vco2_ena);
          $fwrite(file, "%1b // jtag_chain43 vco2_byp_clk_sel\n", reg_vco2_byp_clk_sel);
          $fwrite(file, "%1b // jtag_chain44 vco2_post_div[0]\n", reg_vco2_post_div[0]);
          $fwrite(file, "%1b // jtag_chain45 vco2_post_div[1]\n", reg_vco2_post_div[1]);
          $fwrite(file, "%1b // jtag_chain46 int_gain[0]\n", reg_int_gain[0]);
          $fwrite(file, "%1b // jtag_chain47 int_gain[1]\n", reg_int_gain[1]);
          $fwrite(file, "%1b // jtag_chain48 int_gain[2]\n", reg_int_gain[2]);
          $fwrite(file, "%1b // jtag_chain49 int_gain[3]\n", reg_int_gain[3]);
          $fwrite(file, "%1b // jtag_chain50 int_gain[4]\n", reg_int_gain[4]);
          $fwrite(file, "%1b // jtag_chain51 prop_gain[0]\n", reg_prop_gain[0]);
          $fwrite(file, "%1b // jtag_chain52 prop_gain[1]\n", reg_prop_gain[1]);
          $fwrite(file, "%1b // jtag_chain53 prop_gain[2]\n", reg_prop_gain[2]);
          $fwrite(file, "%1b // jtag_chain54 prop_gain[3]\n", reg_prop_gain[3]);
          $fwrite(file, "%1b // jtag_chain55 prop_gain[4]\n", reg_prop_gain[4]);
          $fwrite(file, "%1b // jtag_chain56 pll_en\n", reg_pll_en);
          $fwrite(file, "%1b // jtag_chain57 pll_reset\n", reg_pll_reset);
          $fwrite(file, "%1b // jtag_chain58 fbdiv_sel[0]\n", reg_fbdiv_sel[0]);
          $fwrite(file, "%1b // jtag_chain59 fbdiv_sel[1]\n", reg_fbdiv_sel[1]);
          $fwrite(file, "%1b // jtag_chain60 fbdiv_sel[2]\n", reg_fbdiv_sel[2]);
          $fwrite(file, "%1b // jtag_chain61 fbdiv_sel[3]\n", reg_fbdiv_sel[3]);
          $fwrite(file, "%1b // jtag_chain62 fbdiv_sel[4]\n", reg_fbdiv_sel[4]);
          $fwrite(file, "%1b // jtag_chain63 fbdiv_sel[5]\n", reg_fbdiv_sel[5]);
          $fwrite(file, "%1b // jtag_chain64 fbdiv_sel[6]\n", reg_fbdiv_sel[6]);
          $fwrite(file, "%1b // jtag_chain65 fbdiv_sel[7]\n", reg_fbdiv_sel[7]);
          $fwrite(file, "%1b // jtag_chain66 fbdiv_sel[8]\n", reg_fbdiv_sel[8]);
          $fwrite(file, "%1b // jtag_chain67 vco_sel[0]\n", reg_vco_sel[0]);
          $fwrite(file, "%1b // jtag_chain68 vco_sel[1]\n", reg_vco_sel[1]);
          $fwrite(file, "%1b // jtag_chain69 bias_lvl[0]\n", reg_bias_lvl[0]);
          $fwrite(file, "%1b // jtag_chain70 bias_lvl[1]\n", reg_bias_lvl[1]);
          $fwrite(file, "%1b // jtag_chain71 bias_lvl[2]\n", reg_bias_lvl[2]);
          $fwrite(file, "%1b // jtag_chain72 bias_lvl[3]\n", reg_bias_lvl[3]);
          $fwrite(file, "%1b // jtag_chain73 div16en\n", reg_div16en);
          $fwrite(file, "%1b // jtag_chain74 bias_sel\n", reg_bias_sel);
          $fwrite(file, "%1b // jtag_chain75 prop_c_ctrl[0]\n", reg_prop_c_ctrl[0]);
          $fwrite(file, "%1b // jtag_chain76 prop_c_ctrl[1]\n", reg_prop_c_ctrl[1]);
          $fwrite(file, "%1b // jtag_chain77 prop_r_ctrl[0]\n", reg_prop_r_ctrl[0]);
          $fwrite(file, "%1b // jtag_chain78 prop_r_ctrl[1]\n", reg_prop_r_ctrl[1]);
          $fwrite(file, "%1b // jtag_chain79 pfd_mode[0]\n", reg_pfd_mode[0]);
          $fwrite(file, "%1b // jtag_chain80 pfd_mode[1]\n", reg_pfd_mode[1]);
          $fwrite(file, "%1b // jtag_chain81 sel_refclk_alt\n", reg_sel_refclk_alt);
 
        end
      end
    end  
  end
  `endif
endmodule


      
//JTAG BSR Flop
module mvp_pll_jtag_bsr(
  input  wire tck,
  input  wire trst_n,
  input  wire bscan_mode,
  input  wire capturedr,      
  input  wire shiftdr,
  input  wire updatedr,
  input  wire pi,
  output wire po,
  input  wire tdi,
  output wire tdo
);


wav_jtag_bsr u_wav_jtag_bsr (
  .i_tck         ( tck            ),     
  .i_trst_n      ( trst_n         ),     
  .i_bsr_mode    ( bscan_mode     ),     
  .i_capture     ( capturedr      ),       
  .i_shift       ( shiftdr        ),       
  .i_update      ( updatedr       ),       
  .i_pi          ( pi             ),       
  .o_po          ( po             ),       
  .i_tdi         ( tdi            ),       
  .o_tdo         ( tdo            )); 
  
endmodule
