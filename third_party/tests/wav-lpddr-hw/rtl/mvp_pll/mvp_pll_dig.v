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

module mvp_pll_dig(
  input  wire                     core_scan_asyncrst_ctrl,                   
  input  wire                     core_scan_clk,                             
  input  wire                     core_scan_mode,   
  input  wire                     core_scan_in,
  output wire                     core_scan_out,
  
  input  wire                     iddq_mode,
  
  input  wire                     bscan_mode,
  input  wire                     bscan_tck,
  input  wire                     bscan_trst_n,
  input  wire                     bscan_capturedr,
  input  wire                     bscan_shiftdr,
  input  wire                     bscan_updatedr,
  input  wire                     bscan_tdi,
  output wire                     bscan_tdo,

  
  // AHB Slave
  input  wire                     hclk,
  input  wire                     hreset,
  input  wire                     hsel,
  input  wire                     hwrite,
  input  wire [1:0]               htrans,
  input  wire [2:0]               hsize,   
  input  wire [2:0]               hburst,  
  input  wire [7:0]               haddr,
  input  wire [31:0]              hwdata,
  output wire [31:0]              hrdata,
  output wire [1:0]               hresp,
  output wire                     hready,
    
  //Core 
  input  wire                     core_reset,
  input  wire [1:0]               core_vco_sel,
  input  wire                     core_switch_vco,
  output wire                     core_gfcm_sel,
  output wire                     core_initial_switch_done,
  output wire                     core_ready,
  output wire [31:0]              core_debug_bus_ctrl_status,
  
  output wire                     interrupt,
  
  // Analog
  output wire [3:0]               mvp_bias_lvl,
  output wire                     mvp_bias_sel,
  output wire                     mvp_cp_int_mode,
                                  
  output wire                     mvp_en,
  input  wire                     mvp_fbclk,
  output wire [8:0]               mvp_fbdiv_sel,
  output wire [4:0]               mvp_int_ctrl,
  output wire [4:0]               mvp_prop_ctrl,
  output wire [1:0]               mvp_pfd_mode,
  output wire [1:0]               mvp_prop_c_ctrl,
  output wire [1:0]               mvp_prop_r_ctrl,
  input  wire                     mvp_refclk,
  output wire                     mvp_reset,
  output wire                     mvp_sel_refclk_alt,
  output wire                     mvp_div16_ena,
  
  input  wire                     mvp_vco0_div2clk,   
  output wire [5:0]               mvp_vco0_band,
  output wire [5:0]               mvp_vco0_fine,
  output wire                     mvp_vco0_byp_clk_sel,
  output wire                     mvp_vco0_ena,
  
  input  wire                     mvp_vco1_div2clk,   
  output wire [5:0]               mvp_vco1_band,
  output wire [5:0]               mvp_vco1_fine,
  output wire                     mvp_vco1_byp_clk_sel,
  output wire                     mvp_vco1_ena,
  output wire [1:0]               mvp_vco1_post_div,
  
  input  wire                     mvp_vco2_div2clk,   
  output wire [5:0]               mvp_vco2_band,
  output wire [5:0]               mvp_vco2_fine,
  output wire                     mvp_vco2_byp_clk_sel,
  output wire                     mvp_vco2_ena,
  output wire [1:0]               mvp_vco2_post_div,
  output wire [1:0]               mvp_vco_sel
  
);


localparam  VCO0  = 'd0,
            VCO1  = 'd1,
            VCO2  = 'd2;

wire          hclk_scan;
wire          hreset_sync;
wire          refclk_scan;
wire          refclk_reset;
wire          fbclk_scan;
wire          fbclk_reset;

wire          vco0_clk_en;
wire          vco0_clk_scan;
wire          vco0_clk_reset;

wire          vco1_clk_en;
wire          vco1_clk_scan;
wire          vco1_clk_reset;

wire          vco2_clk_en;
wire          vco2_clk_scan;
wire          vco2_clk_reset;




wire          en_lock_det;
wire          en_fastlock;
wire          locked;
wire [1:0]    sm_vco_sel;
wire          ready_int;
wire          enable_fbclk;


wire          swi_core_reset_muxed;
wire  [1:0]   swi_core_vco_sel_muxed;

wire [5:0]    vco0_band_fll;
wire [5:0]    vco0_fine_fll;
wire  [8:0]   swi_vco0_int;
wire  [15:0]  swi_vco0_frac;
wire          swi_vco0_frac_en;
wire          swi_vco0_frac_en_auto;
wire          swi_vco0_fll_enable;
wire          swi_vco0_fll_manual_mode;
wire  [5:0]   swi_vco0_band_start;
wire  [3:0]   swi_vco0_delay_count;
wire          swi_vco0_use_demeted_check;
wire  [3:0]   swi_vco0_locked_count_threshold;
wire          vco0_too_fast_status ;
wire          vco0_too_slow_status ;
wire          vco0_locked ;
wire  [7:0]   swi_vco0_fll_refclk_count;
wire  [15:0]  swi_vco0_fll_vco_count_target;
wire  [4:0]   swi_vco0_fll_range;
wire  [5:0]   vco0_band_prev_status;
wire  [5:0]   vco0_fine_prev_status;
wire  [5:0]   swi_vco0_fll_band_thresh;
wire  [15:0]  vco0_vco_count;
wire  [5:0]   swi_vco0_fine_start;
wire          swi_vco0_fll_bypass_band;
wire          swi_vco0_fll_bypass_fine;
wire          swi_vco0_fll_persistent_mode;

wire [5:0]    vco1_band_fll;
wire [5:0]    vco1_fine_fll;
wire  [8:0]   swi_vco1_int;
wire  [15:0]  swi_vco1_frac;
wire          swi_vco1_frac_en;
wire          swi_vco1_frac_en_auto;
wire          swi_vco1_fll_enable;
wire          swi_vco1_fll_manual_mode;
wire  [5:0]   swi_vco1_band_start;
wire  [3:0]   swi_vco1_delay_count;
wire          swi_vco1_use_demeted_check;
wire  [3:0]   swi_vco1_locked_count_threshold;
wire          vco1_too_fast_status ;
wire          vco1_too_slow_status ;
wire          vco1_locked ;
wire  [7:0]   swi_vco1_fll_refclk_count;
wire  [15:0]  swi_vco1_fll_vco_count_target;
wire  [4:0]   swi_vco1_fll_range;
wire  [5:0]   vco1_band_prev_status ;
wire  [5:0]   vco1_fine_prev_status;
wire  [5:0]   swi_vco1_fll_band_thresh;
wire  [15:0]  vco1_vco_count;
wire          swi_vco1_ssc_enable;
wire  [9:0]   swi_vco1_ssc_stepsize;
wire  [16:0]  swi_vco1_ssc_amp;
wire          swi_vco1_ssc_count_cycles;
wire          swi_vco1_ssc_center_spread;
wire  [5:0]   swi_vco1_fine_start;
wire          swi_vco1_fll_bypass_band;
wire          swi_vco1_fll_bypass_fine;
wire          swi_vco1_fll_persistent_mode;

wire [5:0]    vco2_band_fll;
wire [5:0]    vco2_fine_fll;
wire  [8:0]   swi_vco2_int;
wire  [15:0]  swi_vco2_frac;
wire          swi_vco2_frac_en;
wire          swi_vco2_frac_en_auto;
wire          swi_vco2_fll_enable;
wire          swi_vco2_fll_manual_mode;
wire  [5:0]   swi_vco2_band_start;
wire  [3:0]   swi_vco2_delay_count;
wire          swi_vco2_use_demeted_check;
wire  [3:0]   swi_vco2_locked_count_threshold;
wire          vco2_too_fast_status ;
wire          vco2_too_slow_status ;
wire          vco2_locked ;
wire  [7:0]   swi_vco2_fll_refclk_count;
wire  [15:0]  swi_vco2_fll_vco_count_target;
wire  [4:0]   swi_vco2_fll_range;
wire  [5:0]   vco2_band_prev_status ;
wire  [5:0]   vco2_fine_prev_status;
wire  [5:0]   swi_vco2_fll_band_thresh;
wire  [15:0]  vco2_vco_count;
wire          swi_vco2_ssc_enable;
wire  [9:0]   swi_vco2_ssc_stepsize;
wire  [16:0]  swi_vco2_ssc_amp;
wire          swi_vco2_ssc_count_cycles;
wire          swi_vco2_ssc_center_spread;
wire  [5:0]   swi_vco2_fine_start;
wire          swi_vco2_fll_bypass_band;
wire          swi_vco2_fll_bypass_fine;
wire          swi_vco2_fll_persistent_mode;

wire  [7:0]   swi_bias_settle_count;
wire  [7:0]   swi_pre_locking_count;
wire  [3:0]   swi_switch_count;
wire          swi_disable_lock_det_after_lock;
wire          swi_force_fbclk_gate;
wire          swi_force_vco0_clk_gate;
wire          swi_force_vco1_clk_gate;
wire          swi_force_vco2_clk_gate;

wire  [3:0]   swi_fll_initial_settle;
wire  [15:0]  swi_ld_refclk_cycles;
wire  [5:0]   swi_ld_range;
wire  [15:0]  swi_fastld_refclk_cycles;
wire  [5:0]   swi_fastld_range;

wire  [4:0]   mvp_int_gain_pre, mvp_prop_gain_pre;
wire  [4:0]   swi_normal_int_gain;
wire  [4:0]   swi_fl_int_gain;
wire  [4:0]   swi_fl_prop_gain;
wire  [4:0]   swi_vco0_prop_gain;
wire  [4:0]   swi_vco1_prop_gain;
wire  [4:0]   swi_vco2_prop_gain;

wire          wfifo_core_switch_vco;
wire          wfifo_winc_core_switch_vco;
wire          core_switch_vco_refclk;

wire          fastlock_ready;
wire          w1c_in_loss_of_lock;
wire          w1c_out_loss_of_lock;
wire          w1c_in_vco0_fll_threshold;
wire          w1c_in_vco1_fll_threshold;
wire          w1c_in_vco2_fll_threshold;
wire          w1c_out_vco0_fll_threshold;
wire          w1c_out_vco1_fll_threshold;
wire          w1c_out_vco2_fll_threshold;
wire          swi_loss_of_lock_int_en;
wire          swi_vco0_fll_threshold_int_en;
wire          swi_vco1_fll_threshold_int_en;
wire          swi_vco2_fll_threshold_int_en;
wire          w1c_out_core_locked;
wire          w1c_out_vco0_fll_locked;
wire          w1c_out_vco1_fll_locked;
wire          w1c_out_vco2_fll_locked;
wire          swi_core_locked_int_en;
wire          swi_vco0_fll_locked_int_en;
wire          swi_vco1_fll_locked_int_en;
wire          swi_vco2_fll_locked_int_en;
wire          swi_en_lock_det_muxed;
wire [3:0]    fsm_state;
wire          w1c_in_initial_switch_done;
wire          w1c_out_initial_switch_done;
wire          swi_initial_switch_done_int_en;
wire          vco0_en_sm;
wire          vco0_en_fll;
wire          vco0_clk_en_fll;
wire          vco1_en_sm;
wire          vco1_en_fll;
wire          vco1_clk_en_fll;
wire          vco2_en_sm;
wire          vco2_en_fll;
wire          vco2_clk_en_fll;
wire          pll_reset_sm;
wire  [16:0]  freq_detect_cycles ;
wire          sm_gfcm_sel;
wire  [3:0]   swi_pre_switch_time;
wire  [3:0]   swi_switch_reset_time;
wire  [7:0]   swi_switch_1_time;
wire  [7:0]   swi_switch_2_time;


assign vco0_clk_en  = vco0_clk_en_fll || swi_force_vco0_clk_gate;
assign vco1_clk_en  = vco1_clk_en_fll || swi_force_vco1_clk_gate;
assign vco2_clk_en  = vco2_clk_en_fll || swi_force_vco2_clk_gate;

mvp_pll_clk_control u_mvp_pll_clk_control (
  .core_scan_asyncrst_ctrl     ( core_scan_asyncrst_ctrl      ),     
  .core_scan_clk               ( core_scan_clk                ),     
  .core_scan_mode              ( core_scan_mode               ),     
  .hclk                        ( hclk                         ),     
  .hclk_scan                   ( hclk_scan                    ),     
  .hreset                      ( hreset                       ),     
  .hreset_sync                 ( hreset_sync                  ),     
  .core_reset                  ( swi_core_reset_muxed         ),  
  .refclk                      ( mvp_refclk                   ),        
  .refclk_scan                 ( refclk_scan                  ),        
  .refclk_reset                ( refclk_reset                 ),        
  .fbclk                       ( mvp_fbclk                    ),  
  .enable_fbclk                ( enable_fbclk || 
                                 swi_force_fbclk_gate         ),
  .fbclk_reset_in              ( ~enable_fbclk                ),  //temp, may add separate signal
  .fbclk_scan                  ( fbclk_scan                   ),            
  .fbclk_reset                 ( fbclk_reset                  ),     
  .vco0_clk                    ( mvp_vco0_div2clk             ),
  .vco0_clk_en                 ( vco0_clk_en                  ),     
  .vco0_clk_scan               ( vco0_clk_scan                ),        
  .vco0_clk_reset              ( vco0_clk_reset               ),       
  .vco1_clk                    ( mvp_vco1_div2clk             ),
  .vco1_clk_en                 ( vco1_clk_en                  ),     
  .vco1_clk_scan               ( vco1_clk_scan                ),        
  .vco1_clk_reset              ( vco1_clk_reset               ),  
  .vco2_clk                    ( mvp_vco2_div2clk             ),  
  .vco2_clk_en                 ( vco2_clk_en                  ),
  .vco2_clk_scan               ( vco2_clk_scan                ),  
  .vco2_clk_reset              ( vco2_clk_reset               )); 




//Used to issue the VCO Sel change request to the state machine
//If using HW version (port on this module) then it uses the rising edge to cause a pulse
wire swi_core_switch_vco_hw_muxed_hclk;
reg  swi_core_switch_vco_hw_muxed_hclk_ff3;
wire swi_core_switch_vco_hw_muxed_hclk_posedge;
demet_reset u_demet_reset_core_switch_vco_hw (
  .clk     ( hclk_scan                                ),              
  .reset   ( hreset_sync                             ),              
  .sig_in  ( swi_core_switch_vco_hw_muxed            ),   
  .sig_out ( swi_core_switch_vco_hw_muxed_hclk       )); 

always @(posedge hclk_scan or posedge hreset_sync) begin
  if(hreset_sync) begin
    swi_core_switch_vco_hw_muxed_hclk_ff3 <= 1'b0;
  end else begin
    swi_core_switch_vco_hw_muxed_hclk_ff3 <= swi_core_switch_vco_hw_muxed_hclk;
  end
end

assign swi_core_switch_vco_hw_muxed_hclk_posedge = swi_core_switch_vco_hw_muxed_hclk && ~swi_core_switch_vco_hw_muxed_hclk_ff3;

mvp_sync_pulse u_mvp_sync_pulse (
  .clk_in          ( hclk_scan                                  ),           
  .clk_in_reset    ( hreset_sync                                ),           
  .data_in         ( (wfifo_core_switch_vco &&
                      wfifo_winc_core_switch_vco) ||
                      swi_core_switch_vco_hw_muxed_hclk_posedge ),           
  .clk_out         ( refclk_scan                                ),           
  .clk_out_reset   ( refclk_reset                               ),           
  .data_out        ( core_switch_vco_refclk                     )); 

mvp_pll_sm u_mvp_pll_sm (
  .clk                                 ( refclk_scan                          ),  
  .reset                               ( refclk_reset                         ),  
  .enable                              ( ~refclk_reset                        ),  //Give overrides?
  .core_vco_sel                        ( swi_core_vco_sel_muxed               ),  
  .core_switch_vco                     ( core_switch_vco_refclk               ),
  .swi_bias_settle_count               ( swi_bias_settle_count                ),  
  .swi_pre_locking_count               ( swi_pre_locking_count                ),  
  .swi_switch_count                    ( swi_switch_count                     ),           
  .swi_disable_lock_det_after_lock     ( swi_disable_lock_det_after_lock      ),  
  
  .swi_pre_switch_time                 ( swi_pre_switch_time                  ),
  .swi_switch_reset_time               ( swi_switch_reset_time                ),
  .swi_switch_1_time                   ( swi_switch_1_time                    ),
  .swi_switch_2_time                   ( swi_switch_2_time                    ),
  
  .en_lock_det                         ( en_lock_det                          ),            
  .en_fastlock                         ( en_fastlock                          ),  
  .locked                              ( locked                               ),  
  .switch_done                         ( w1c_in_initial_switch_done           ),
  .enable_fbclk                        ( enable_fbclk                         ),
  .pll_reset                           ( pll_reset_sm                         ),
  .vctrl_locked                        ( /*noconn*/                           ),
  .vco_sel                             ( sm_vco_sel                           ),    
  .vco_gfcm_sel                        ( sm_gfcm_sel                          ),
  .vco1_en                             ( vco1_en_sm                           ),
  .vco2_en                             ( vco2_en_sm                           ),
    
  .fastlock_ready                      ( fastlock_ready                       ),     
  .ready                               ( ready_int                            ),
  .loss_of_lock                        ( w1c_in_loss_of_lock                  ),
  .fsm_state                           ( fsm_state                            )); 




mvp_fll u_mvp_fll_VCO0 (
  .refclk                     ( refclk_scan                       ),  
  .refclk_reset               ( refclk_reset                      ),  
  .vco_clk                    ( vco0_clk_scan                     ),     
  .vco_clk_reset              ( vco0_clk_reset                    ),     
  .enable                     ( swi_vco0_fll_enable               ),  
  .swi_manual_mode            ( swi_vco0_fll_manual_mode          ),
  .swi_ref_count              ( swi_vco0_fll_refclk_count         ),     
  .swi_vco_count_target       ( swi_vco0_fll_vco_count_target     ),     
  .swi_range                  ( swi_vco0_fll_range                ),   
  .swi_delay_count            ( swi_vco0_delay_count              ),  
  .swi_use_demeted_check      ( swi_vco0_use_demeted_check        ), 
  .swi_locked_count_threshold ( swi_vco0_locked_count_threshold   ),
  .swi_vco_band_start         ( swi_vco0_band_start               ),  
  .swi_vco_fine_start         ( swi_vco0_fine_start               ),
  .swi_fll_initial_settle     ( swi_fll_initial_settle            ),
  .swi_fll_band_thresh        ( swi_vco0_fll_band_thresh          ),
  .swi_bypass_band            ( swi_vco0_fll_bypass_band          ),
  .swi_bypass_fine            ( swi_vco0_fll_bypass_fine          ),
  .swi_persistent_mode        ( swi_vco0_fll_persistent_mode      ),
  .fll_band_thresh_hit        ( w1c_in_vco0_fll_threshold         ),
  .en_vco                     ( vco0_en_fll                       ),
  .en_clk                     ( vco0_clk_en_fll                   ),
  .vco_too_fast_status        ( vco0_too_fast_status              ),
  .vco_too_slow_status        ( vco0_too_slow_status              ),
  .vco_band_prev              ( vco0_band_prev_status             ),
  .vco_band                   ( vco0_band_fll                     ),
  .vco_fine_prev              ( vco0_fine_prev_status             ),
  .vco_fine                   ( vco0_fine_fll                     ),
  .vco_count_status           ( vco0_vco_count                    ),
  .locked                     ( vco0_locked                       )); 

mvp_fll u_mvp_fll_VCO1 (
  .refclk                     ( refclk_scan                       ),  
  .refclk_reset               ( refclk_reset                      ),  
  .vco_clk                    ( vco1_clk_scan                     ),     
  .vco_clk_reset              ( vco1_clk_reset                    ),     
  .enable                     ( swi_vco1_fll_enable               ),  
  .swi_manual_mode            ( swi_vco1_fll_manual_mode          ),
  .swi_ref_count              ( swi_vco1_fll_refclk_count         ),     
  .swi_vco_count_target       ( swi_vco1_fll_vco_count_target     ),     
  .swi_range                  ( swi_vco1_fll_range                ),   
  .swi_delay_count            ( swi_vco1_delay_count              ),  
  .swi_use_demeted_check      ( swi_vco1_use_demeted_check        ), 
  .swi_locked_count_threshold ( swi_vco1_locked_count_threshold   ),
  .swi_vco_band_start         ( swi_vco1_band_start               ),
  .swi_vco_fine_start         ( swi_vco1_fine_start               ),
  .swi_fll_initial_settle     ( swi_fll_initial_settle            ),  
  .swi_fll_band_thresh        ( swi_vco1_fll_band_thresh          ),
  .swi_bypass_band            ( swi_vco1_fll_bypass_band          ),
  .swi_bypass_fine            ( swi_vco1_fll_bypass_fine          ),
  .swi_persistent_mode        ( swi_vco1_fll_persistent_mode      ),
  .fll_band_thresh_hit        ( w1c_in_vco1_fll_threshold         ),
  .en_vco                     ( vco1_en_fll                       ),
  .en_clk                     ( vco1_clk_en_fll                   ),
  .vco_too_fast_status        ( vco1_too_fast_status              ),
  .vco_too_slow_status        ( vco1_too_slow_status              ),
  .vco_band_prev              ( vco1_band_prev_status             ),
  .vco_band                   ( vco1_band_fll                     ),
  .vco_fine_prev              ( vco1_fine_prev_status             ),
  .vco_fine                   ( vco1_fine_fll                     ),
  .vco_count_status           ( vco1_vco_count                    ),
  .locked                     ( vco1_locked                       )); 


mvp_fll u_mvp_fll_VCO2 (
  .refclk                     ( refclk_scan                       ),  
  .refclk_reset               ( refclk_reset                      ),  
  .vco_clk                    ( vco2_clk_scan                     ),   
  .vco_clk_reset              ( vco2_clk_reset                    ),   
  .enable                     ( swi_vco2_fll_enable               ),  
  .swi_manual_mode            ( swi_vco2_fll_manual_mode          ),
  .swi_ref_count              ( swi_vco2_fll_refclk_count         ),  
  .swi_vco_count_target       ( swi_vco2_fll_vco_count_target     ),  
  .swi_range                  ( swi_vco2_fll_range                ),  
  .swi_delay_count            ( swi_vco2_delay_count              ),  
  .swi_use_demeted_check      ( swi_vco2_use_demeted_check        ),  
  .swi_locked_count_threshold ( swi_vco2_locked_count_threshold   ),
  .swi_vco_band_start         ( swi_vco2_band_start               ),  
  .swi_vco_fine_start         ( swi_vco2_fine_start               ),
  .swi_fll_initial_settle     ( swi_fll_initial_settle            ),
  .swi_fll_band_thresh        ( swi_vco2_fll_band_thresh          ),
  .swi_bypass_band            ( swi_vco2_fll_bypass_band          ),
  .swi_bypass_fine            ( swi_vco2_fll_bypass_fine          ),
  .swi_persistent_mode        ( swi_vco2_fll_persistent_mode      ),
  .fll_band_thresh_hit        ( w1c_in_vco2_fll_threshold         ),
  .en_vco                     ( vco2_en_fll                       ),
  .en_clk                     ( vco2_clk_en_fll                   ),
  .vco_too_fast_status        ( vco2_too_fast_status              ),
  .vco_too_slow_status        ( vco2_too_slow_status              ),
  .vco_band_prev              ( vco2_band_prev_status             ),
  .vco_band                   ( vco2_band_fll                     ),
  .vco_fine_prev              ( vco2_fine_prev_status             ),
  .vco_fine                   ( vco2_fine_fll                     ),
  .vco_count_status           ( vco2_vco_count                    ),
  .locked                     ( vco2_locked                       )); 



wire [17:0]   sscout;
wire          ssc_enable;
wire  [9:0]   ssc_stepsize;
wire  [16:0]  ssc_amp;
wire          ssc_count_cycles;
wire          ssc_center_spread;

assign ssc_enable         = (sm_vco_sel == VCO1) ? swi_vco1_ssc_enable && core_ready : swi_vco2_ssc_enable && core_ready;
assign ssc_stepsize       = (sm_vco_sel == VCO1) ? swi_vco1_ssc_stepsize             : swi_vco2_ssc_stepsize;
assign ssc_amp            = (sm_vco_sel == VCO1) ? swi_vco1_ssc_amp                  : swi_vco2_ssc_amp;
assign ssc_count_cycles   = (sm_vco_sel == VCO1) ? swi_vco1_ssc_count_cycles         : swi_vco2_ssc_count_cycles;
assign ssc_center_spread  = (sm_vco_sel == VCO1) ? swi_vco1_ssc_center_spread        : swi_vco2_ssc_center_spread;
                                            

pll_ssc #(
  //parameters
  .AMPLITUDE_WIDTH    ( 17        ),
  .SSC_WIDTH          ( 18        ),
  .STEPSIZE_WIDTH     ( 10        )
) u_mvp_pll_ssc (
  .clk             ( fbclk_scan               ),  
  .reset           ( fbclk_reset              ),  
  .stepsize        ( ssc_stepsize             ),      
  .amplitude       ( ssc_amp                  ),       
  .enable          ( ssc_enable               ),  
  .count_cycles    ( ssc_count_cycles         ),  
  .centerspread    ( ssc_center_spread        ),  
  .sscout          ( sscout                   )); 


wire [8:0]  integer_val_selected;
wire [15:0] frac_val_selected;
wire        frac_en_selected;
wire [8:0]  fbdiv_out;

assign integer_val_selected = (sm_vco_sel == VCO0) ? swi_vco0_int   : 
                              (sm_vco_sel == VCO1) ? swi_vco1_int   : swi_vco2_int;
                              
assign frac_val_selected    = (sm_vco_sel == VCO0) ? swi_vco0_frac  : 
                              (sm_vco_sel == VCO1) ? swi_vco1_frac  : swi_vco2_frac;
                              
assign frac_en_selected     = (sm_vco_sel == VCO0) ? (swi_vco0_frac_en_auto ? (|swi_vco0_frac) : swi_vco0_frac_en) :
                              (sm_vco_sel == VCO1) ? (swi_vco1_frac_en_auto ? (|swi_vco1_frac) : swi_vco1_frac_en) : 
                                                     (swi_vco2_frac_en_auto ? (|swi_vco2_frac) : swi_vco2_frac_en);


pll_mash u_mvp_pll_mash (
  .clk             ( fbclk_scan                    ),  
  .reset           ( fbclk_reset                   ),  
  .frac            ( frac_val_selected             ),  
  .intg            ( integer_val_selected          ),  
  .sscoffsetin     ( sscout                        ),  
  .frac_en         ( frac_en_selected              ),  
  .divout          ( fbdiv_out                     )); 


wire [5:0]  fd_range_sel;
wire [15:0] fd_refclk_cycles_sel;

assign fd_range_sel         = en_fastlock ? swi_fastld_range          : swi_ld_range;
assign fd_refclk_cycles_sel = en_fastlock ? swi_fastld_refclk_cycles  : swi_ld_refclk_cycles;
pll_freq_detect #(
  //parameters
  .FB_WIDTH           ( 17        ),
  .REF_WIDTH          ( 16        )
) u_mvp_pll_freq_detect (
  .ref_clk     ( refclk_scan                  ),            
  .ref_reset   ( refclk_reset                 ),            
  .fb_clk      ( fbclk_scan                   ),            
  .fb_reset    ( fbclk_reset                  ),            
  .enable      ( swi_en_lock_det_muxed        ),  
  .range       ( fd_range_sel                 ),  
  .ref_cycles  ( fd_refclk_cycles_sel         ),        
  .fb_target   ( {1'b0, fd_refclk_cycles_sel} ),  //Same as refclk since ideal refclk == fbclk
  .fb_cycles   ( freq_detect_cycles           ),       
  .match       ( locked                       )); 
  

assign mvp_int_gain_pre = en_fastlock          ? swi_fl_int_gain    : swi_normal_int_gain;

assign mvp_prop_gain_pre= en_fastlock          ? swi_fl_prop_gain   : 
                          (sm_vco_sel == VCO0) ? swi_vco0_prop_gain :
                          (sm_vco_sel == VCO1) ? swi_vco1_prop_gain : swi_vco2_prop_gain;


assign core_ready = ready_int; 
assign core_initial_switch_done = w1c_in_initial_switch_done;

//Since we expect VCO0 to run almost all the time
//User can still override
assign vco0_en_sm = mvp_en;
//assign vco1_en_sm = (sm_vco_sel == VCO1) && mvp_en;
//assign vco2_en_sm = (sm_vco_sel == VCO2) && mvp_en;





mvp_pll_regs_top #(
  //parameters
  .ADDR_WIDTH         ( 8         )
) u_mvp_pll_regs_top (
  .core_reset                        ( core_reset                                                           ), 
  .swi_core_reset_muxed              ( swi_core_reset_muxed                                                 ), 
  .core_vco_sel                      ( core_vco_sel                                                         ), 
  .swi_core_vco_sel_muxed            ( swi_core_vco_sel_muxed                                               ), 
  .core_gfcm_sel                     ( sm_gfcm_sel                                                          ), 
  .swi_core_gfcm_sel_muxed           ( core_gfcm_sel                                                        ), 
  .wfifo_core_switch_vco             ( wfifo_core_switch_vco                                                ), 
  .wfifo_winc_core_switch_vco        ( wfifo_winc_core_switch_vco                                           ), 
  .core_switch_vco_hw                ( core_switch_vco                                                      ), 
  .swi_core_switch_vco_hw_muxed      ( swi_core_switch_vco_hw_muxed                                         ), 
  .core_ready                        ( ready_int                                                            ), 
  .core_fastlock_ready               ( fastlock_ready                                                       ), 
  .core_initial_switch_done          ( core_initial_switch_done                                             ),
  .freq_detect_lock                  ( locked                                                               ), 
  .freq_detect_cycles                ( freq_detect_cycles                                                   ), 
  .fsm_state                         ( fsm_state                                                            ), 
  .w1c_in_loss_of_lock               ( w1c_in_loss_of_lock && swi_loss_of_lock_int_en                       ),  
  .w1c_out_loss_of_lock              ( w1c_out_loss_of_lock                                                 ),  
  .w1c_in_core_locked                ( ready_int && swi_core_locked_int_en                                  ),  
  .w1c_out_core_locked               ( w1c_out_core_locked                                                  ),  
  .w1c_in_initial_switch_done        ( w1c_in_initial_switch_done && swi_initial_switch_done_int_en         ),  
  .w1c_out_initial_switch_done       ( w1c_out_initial_switch_done                                          ),  
  .w1c_in_vco0_fll_locked            ( vco0_locked && swi_vco0_fll_locked_int_en                            ),  
  .w1c_out_vco0_fll_locked           ( w1c_out_vco0_fll_locked                                              ),  
  .w1c_in_vco0_fll_threshold         ( w1c_in_vco0_fll_threshold && swi_vco0_fll_threshold_int_en           ),  
  .w1c_out_vco0_fll_threshold        ( w1c_out_vco0_fll_threshold                                           ),  
  .w1c_in_vco1_fll_locked            ( vco1_locked && swi_vco1_fll_locked_int_en                            ),  
  .w1c_out_vco1_fll_locked           ( w1c_out_vco1_fll_locked                                              ),  
  .w1c_in_vco1_fll_threshold         ( w1c_in_vco1_fll_threshold && swi_vco1_fll_threshold_int_en           ),  
  .w1c_out_vco1_fll_threshold        ( w1c_out_vco1_fll_threshold                                           ),  
  .w1c_in_vco2_fll_locked            ( vco2_locked && swi_vco2_fll_locked_int_en                            ),  
  .w1c_out_vco2_fll_locked           ( w1c_out_vco2_fll_locked                                              ),  
  .w1c_in_vco2_fll_threshold         ( w1c_in_vco2_fll_threshold && swi_vco2_fll_threshold_int_en           ),  
  .w1c_out_vco2_fll_threshold        ( w1c_out_vco2_fll_threshold                                           ), 
  .swi_loss_of_lock_int_en           ( swi_loss_of_lock_int_en                                              ), 
  .swi_core_locked_int_en            ( swi_core_locked_int_en                                               ), 
  .swi_initial_switch_done_int_en    ( swi_initial_switch_done_int_en                                       ), 
  .swi_vco0_fll_locked_int_en        ( swi_vco0_fll_locked_int_en                                           ), 
  .swi_vco0_fll_threshold_int_en     ( swi_vco0_fll_threshold_int_en                                        ), 
  .swi_vco1_fll_locked_int_en        ( swi_vco1_fll_locked_int_en                                           ), 
  .swi_vco1_fll_threshold_int_en     ( swi_vco1_fll_threshold_int_en                                        ), 
  .swi_vco2_fll_locked_int_en        ( swi_vco2_fll_locked_int_en                                           ), 
  .swi_vco2_fll_threshold_int_en     ( swi_vco2_fll_threshold_int_en                                        ), 
  .vco0_band                         ( vco0_band_fll                                                        ), 
  .swi_vco0_band_muxed               ( mvp_vco0_band                                                        ), 
  .vco0_fine                         ( vco0_fine_fll                                                        ), 
  .swi_vco0_fine_muxed               ( mvp_vco0_fine                                                        ), 
  .vco0_ena                          ( vco0_en_fll || vco0_en_sm                                            ), 
  .swi_vco0_ena_muxed                ( mvp_vco0_ena                                                         ), 
  .swi_vco0_byp_clk_sel              ( mvp_vco0_byp_clk_sel                                                 ), 
  .swi_vco0_fll_enable               ( swi_vco0_fll_enable                                                  ), 
  .swi_vco0_fll_manual_mode          ( swi_vco0_fll_manual_mode                                             ), 
  .swi_vco0_band_start               ( swi_vco0_band_start                                                  ), 
  .swi_vco0_fine_start               ( swi_vco0_fine_start                                                  ), 
  .swi_vco0_delay_count              ( swi_vco0_delay_count                                                 ), 
  .swi_vco0_use_demeted_check        ( swi_vco0_use_demeted_check                                           ), 
  .swi_vco0_locked_count_threshold   ( swi_vco0_locked_count_threshold                                      ), 
  .swi_vco0_fll_bypass_band          ( swi_vco0_fll_bypass_band                                             ), 
  .swi_vco0_fll_bypass_fine          ( swi_vco0_fll_bypass_fine                                             ), 
  .swi_vco0_fll_persistent_mode      ( swi_vco0_fll_persistent_mode                                         ), 
  .vco0_too_fast_status              ( vco0_too_fast_status                                                 ), 
  .vco0_too_slow_status              ( vco0_too_slow_status                                                 ), 
  .vco0_locked                       ( vco0_locked                                                          ), 
  .swi_vco0_fll_refclk_count         ( swi_vco0_fll_refclk_count                                            ), 
  .swi_vco0_fll_vco_count_target     ( swi_vco0_fll_vco_count_target                                        ), 
  .swi_vco0_fll_range                ( swi_vco0_fll_range                                                   ), 
  .swi_vco0_fll_band_thresh          ( swi_vco0_fll_band_thresh                                             ), 
  .vco0_band_status                  ( vco0_band_fll                                                        ), 
  .vco0_band_prev_status             ( vco0_band_prev_status                                                ), 
  .vco0_fine_status                  ( vco0_fine_fll                                                        ), 
  .vco0_fine_prev_status             ( vco0_fine_prev_status                                                ), 
  .vco0_vco_count                    ( vco0_vco_count                                                       ), 
  .swi_vco0_int                      ( swi_vco0_int                                                         ), 
  .swi_vco0_frac                     ( swi_vco0_frac                                                        ), 
  .swi_vco0_frac_en                  ( swi_vco0_frac_en                                                     ), 
  .swi_vco0_frac_en_auto             ( swi_vco0_frac_en_auto                                                ), 
  .swi_vco0_prop_gain                ( swi_vco0_prop_gain                                                   ), 
  .vco1_band                         ( vco1_band_fll                                                        ), 
  .swi_vco1_band_muxed               ( mvp_vco1_band                                                        ), 
  .vco1_fine                         ( vco1_fine_fll                                                        ), 
  .swi_vco1_fine_muxed               ( mvp_vco1_fine                                                        ), 
  .vco1_ena                          ( vco1_en_fll || vco1_en_sm                                            ), 
  .swi_vco1_ena_muxed                ( mvp_vco1_ena                                                         ), 
  .swi_vco1_byp_clk_sel              ( mvp_vco1_byp_clk_sel                                                 ), 
  .swi_vco1_post_div                 ( mvp_vco1_post_div                                                    ), 
  .swi_vco1_fll_enable               ( swi_vco1_fll_enable                                                  ), 
  .swi_vco1_fll_manual_mode          ( swi_vco1_fll_manual_mode                                             ), 
  .swi_vco1_band_start               ( swi_vco1_band_start                                                  ), 
  .swi_vco1_fine_start               ( swi_vco1_fine_start                                                  ), 
  .swi_vco1_delay_count              ( swi_vco1_delay_count                                                 ), 
  .swi_vco1_use_demeted_check        ( swi_vco1_use_demeted_check                                           ), 
  .swi_vco1_locked_count_threshold   ( swi_vco1_locked_count_threshold                                      ), 
  .swi_vco1_fll_bypass_band          ( swi_vco1_fll_bypass_band                                             ), 
  .swi_vco1_fll_bypass_fine          ( swi_vco1_fll_bypass_fine                                             ), 
  .swi_vco1_fll_persistent_mode      ( swi_vco1_fll_persistent_mode                                         ), 
  .vco1_too_fast_status              ( vco1_too_fast_status                                                 ), 
  .vco1_too_slow_status              ( vco1_too_slow_status                                                 ), 
  .vco1_locked                       ( vco1_locked                                                          ), 
  .swi_vco1_fll_refclk_count         ( swi_vco1_fll_refclk_count                                            ), 
  .swi_vco1_fll_vco_count_target     ( swi_vco1_fll_vco_count_target                                        ), 
  .swi_vco1_fll_range                ( swi_vco1_fll_range                                                   ), 
  .swi_vco1_fll_band_thresh          ( swi_vco1_fll_band_thresh                                             ), 
  .vco1_band_status                  ( vco1_band_fll                                                        ), 
  .vco1_band_prev_status             ( vco1_band_prev_status                                                ), 
  .vco1_fine_status                  ( vco1_fine_fll                                                        ), 
  .vco1_fine_prev_status             ( vco1_fine_prev_status                                                ), 
  .vco1_vco_count                    ( vco1_vco_count                                                       ), 
  .swi_vco1_int                      ( swi_vco1_int                                                         ), 
  .swi_vco1_frac                     ( swi_vco1_frac                                                        ), 
  .swi_vco1_frac_en                  ( swi_vco1_frac_en                                                     ), 
  .swi_vco1_frac_en_auto             ( swi_vco1_frac_en_auto                                                ), 
  .swi_vco1_prop_gain                ( swi_vco1_prop_gain                                                   ), 
  .swi_vco1_ssc_enable               ( swi_vco1_ssc_enable                                                  ), 
  .swi_vco1_ssc_stepsize             ( swi_vco1_ssc_stepsize                                                ), 
  .swi_vco1_ssc_amp                  ( swi_vco1_ssc_amp                                                     ), 
  .swi_vco1_ssc_count_cycles         ( swi_vco1_ssc_count_cycles                                            ), 
  .swi_vco1_ssc_center_spread        ( swi_vco1_ssc_center_spread                                           ), 
  .vco2_band                         ( vco2_band_fll                                                        ), 
  .swi_vco2_band_muxed               ( mvp_vco2_band                                                        ), 
  .vco2_fine                         ( vco2_fine_fll                                                        ), 
  .swi_vco2_fine_muxed               ( mvp_vco2_fine                                                        ), 
  .vco2_ena                          ( vco2_en_fll || vco2_en_sm                                            ), 
  .swi_vco2_ena_muxed                ( mvp_vco2_ena                                                         ), 
  .swi_vco2_byp_clk_sel              ( mvp_vco2_byp_clk_sel                                                 ), 
  .swi_vco2_post_div                 ( mvp_vco2_post_div                                                    ), 
  .swi_vco2_fll_enable               ( swi_vco2_fll_enable                                                  ), 
  .swi_vco2_fll_manual_mode          ( swi_vco2_fll_manual_mode                                             ), 
  .swi_vco2_band_start               ( swi_vco2_band_start                                                  ), 
  .swi_vco2_fine_start               ( swi_vco2_fine_start                                                  ), 
  .swi_vco2_delay_count              ( swi_vco2_delay_count                                                 ), 
  .swi_vco2_use_demeted_check        ( swi_vco2_use_demeted_check                                           ), 
  .swi_vco2_locked_count_threshold   ( swi_vco2_locked_count_threshold                                      ), 
  .swi_vco2_fll_bypass_band          ( swi_vco2_fll_bypass_band                                             ), 
  .swi_vco2_fll_bypass_fine          ( swi_vco2_fll_bypass_fine                                             ), 
  .swi_vco2_fll_persistent_mode      ( swi_vco2_fll_persistent_mode                                         ), 
  .vco2_too_fast_status              ( vco2_too_fast_status                                                 ), 
  .vco2_too_slow_status              ( vco2_too_slow_status                                                 ), 
  .vco2_locked                       ( vco2_locked                                                          ), 
  .swi_vco2_fll_refclk_count         ( swi_vco2_fll_refclk_count                                            ), 
  .swi_vco2_fll_vco_count_target     ( swi_vco2_fll_vco_count_target                                        ), 
  .swi_vco2_fll_range                ( swi_vco2_fll_range                                                   ), 
  .swi_vco2_fll_band_thresh          ( swi_vco2_fll_band_thresh                                             ), 
  .vco2_band_status                  ( vco2_band_fll                                                        ), 
  .vco2_band_prev_status             ( vco2_band_prev_status                                                ), 
  .vco2_fine_status                  ( vco2_fine_fll                                                        ), 
  .vco2_fine_prev_status             ( vco2_fine_prev_status                                                ), 
  .vco2_vco_count                    ( vco2_vco_count                                                       ), 
  .swi_vco2_int                      ( swi_vco2_int                                                         ), 
  .swi_vco2_frac                     ( swi_vco2_frac                                                        ), 
  .swi_vco2_frac_en                  ( swi_vco2_frac_en                                                     ), 
  .swi_vco2_frac_en_auto             ( swi_vco2_frac_en_auto                                                ), 
  .swi_vco2_prop_gain                ( swi_vco2_prop_gain                                                   ), 
  .swi_vco2_ssc_enable               ( swi_vco2_ssc_enable                                                  ), 
  .swi_vco2_ssc_stepsize             ( swi_vco2_ssc_stepsize                                                ), 
  .swi_vco2_ssc_amp                  ( swi_vco2_ssc_amp                                                     ), 
  .swi_vco2_ssc_count_cycles         ( swi_vco2_ssc_count_cycles                                            ), 
  .swi_vco2_ssc_center_spread        ( swi_vco2_ssc_center_spread                                           ), 
  .swi_bias_settle_count             ( swi_bias_settle_count                                                ), 
  .swi_pre_locking_count             ( swi_pre_locking_count                                                ), 
  .swi_switch_count                  ( swi_switch_count                                                     ), 
  .swi_disable_lock_det_after_lock   ( swi_disable_lock_det_after_lock                                      ), 
  .swi_fll_initial_settle            ( swi_fll_initial_settle                                               ), 
  .swi_pre_switch_time               ( swi_pre_switch_time                                                  ), 
  .swi_switch_reset_time             ( swi_switch_reset_time                                                ), 
  .swi_switch_1_time                 ( swi_switch_1_time                                                    ), 
  .swi_switch_2_time                 ( swi_switch_2_time                                                    ), 
  .swi_normal_int_gain               ( swi_normal_int_gain                                                  ), 
  .swi_fl_int_gain                   ( swi_fl_int_gain                                                      ), 
  .swi_fl_prop_gain                  ( swi_fl_prop_gain                                                     ), 
  .int_gain                          ( mvp_int_gain_pre                                                     ), 
  .swi_int_gain_muxed                ( mvp_int_ctrl                                                         ), 
  .prop_gain                         ( mvp_prop_gain_pre                                                    ), 
  .swi_prop_gain_muxed               ( mvp_prop_ctrl                                                        ), 
  .swi_ld_refclk_cycles              ( swi_ld_refclk_cycles                                                 ), 
  .swi_ld_range                      ( swi_ld_range                                                         ), 
  .swi_fastld_refclk_cycles          ( swi_fastld_refclk_cycles                                             ), 
  .swi_fastld_range                  ( swi_fastld_range                                                     ), 
  .pll_en                            ( ~swi_core_reset_muxed                                                ), 
  .swi_pll_en_muxed                  ( mvp_en                                                               ), 
  .pll_reset                         ( swi_core_reset_muxed || pll_reset_sm                                 ), 
  .swi_pll_reset_muxed               ( mvp_reset                                                            ), 
  .fbdiv_sel                         ( fbdiv_out                                                            ), 
  .swi_fbdiv_sel_muxed               ( mvp_fbdiv_sel                                                        ), 
  .vco_sel                           ( sm_vco_sel                                                           ), 
  .swi_vco_sel_muxed                 ( mvp_vco_sel                                                          ), 
  .swi_bias_lvl                      ( mvp_bias_lvl                                                         ), 
  .swi_cp_int_mode                   ( mvp_cp_int_mode                                                      ), 
  .en_lock_det                       ( en_lock_det                                                          ), 
  .swi_en_lock_det_muxed             ( swi_en_lock_det_muxed                                                ), 
  .swi_div16en                       ( mvp_div16_ena                                                        ), 
  .swi_bias_sel                      ( mvp_bias_sel                                                         ),
  .swi_prop_c_ctrl                   ( mvp_prop_c_ctrl                                                      ), 
  .swi_prop_r_ctrl                   ( mvp_prop_r_ctrl                                                      ), 
  .swi_pfd_mode                      ( mvp_pfd_mode                                                         ), 
  .swi_sel_refclk_alt                ( mvp_sel_refclk_alt                                                   ), 
  .swi_force_fbclk_gate              ( swi_force_fbclk_gate                                                 ), 
  .swi_force_vco0_clk_gate           ( swi_force_vco0_clk_gate                                              ), 
  .swi_force_vco1_clk_gate           ( swi_force_vco1_clk_gate                                              ), 
  .swi_force_vco2_clk_gate           ( swi_force_vco2_clk_gate                                              ), 
  .debug_bus_ctrl_status             ( core_debug_bus_ctrl_status                                           ), 
  .dft_core_scan_mode                ( core_scan_mode                                                       ), 
  .dft_iddq_mode                     ( iddq_mode                                                            ), 
  .dft_bscan_mode                    ( bscan_mode                                                           ),  
  .dft_bscan_tck                     ( bscan_tck                                                            ),  
  .dft_bscan_trst_n                  ( bscan_trst_n                                                         ),  
  .dft_bscan_capturedr               ( bscan_capturedr                                                      ),  
  .dft_bscan_shiftdr                 ( bscan_shiftdr                                                        ),  
  .dft_bscan_updatedr                ( bscan_updatedr                                                       ),  
  .dft_bscan_tdi                     ( bscan_tdi                                                            ),  
  .dft_bscan_tdo                     ( bscan_tdo                                                            ),  
  .RegReset                          ( hreset_sync                                                          ), 
  .RegClk                            ( hclk_scan                                                            ), 
  .hsel                              ( hsel                                                                 ), 
  .hwrite                            ( hwrite                                                               ), 
  .htrans                            ( htrans                                                               ), 
  .hsize                             ( hsize                                                                ), 
  .hburst                            ( hburst                                                               ), 
  .haddr                             ( haddr                                                                ), 
  .hwdata                            ( hwdata                                                               ), 
  .hrdata                            ( hrdata                                                               ), 
  .hresp                             ( hresp                                                                ), 
  .hready                            ( hready                                                               ));


assign interrupt = w1c_out_loss_of_lock         ||
                   w1c_out_vco0_fll_threshold   ||
                   w1c_out_vco1_fll_threshold   ||
                   w1c_out_vco2_fll_threshold   ||
                   w1c_out_vco0_fll_locked      ||
                   w1c_out_vco1_fll_locked      ||
                   w1c_out_vco2_fll_locked      ||
                   w1c_out_core_locked          ||
                   w1c_out_initial_switch_done ;

endmodule
