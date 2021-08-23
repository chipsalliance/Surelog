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

module mvp_pll_sm(
  input  wire       clk,
  input  wire       reset,
  
  input  wire       enable,
  input  wire [1:0] core_vco_sel,
  input  wire       core_switch_vco,
  input  wire [7:0] swi_bias_settle_count,
  input  wire [7:0] swi_pre_locking_count,
  input  wire [3:0] swi_switch_count,
  input  wire       swi_disable_lock_det_after_lock,
  
  input  wire [3:0] swi_pre_switch_time,
  input  wire [3:0] swi_switch_reset_time,
  input  wire [7:0] swi_switch_1_time,
  input  wire [7:0] swi_switch_2_time,
  
  
  output reg        en_lock_det,
  output reg        en_fastlock,
  input  wire       locked,
  output reg        switch_done,
  output reg        enable_fbclk,
  output reg        pll_reset,
  output reg        vctrl_locked,                     //Indicates we have been through lock at least once
  output wire [1:0] vco_sel,
  output reg        vco_gfcm_sel,
  output reg        vco1_en,
  output reg        vco2_en,
  output reg        fastlock_ready,
  output wire       ready,
  output reg        loss_of_lock,
  output wire [3:0] fsm_state
);

localparam    VCO0  = 'd0,
              VCO1  = 'd1,
              VCO2  = 'd2;
              
localparam    IDLE            = 'd0,
              BIAS_SETTLE     = 'd1,
              FASTLOCKING     = 'd2,
              PRE_LOCKING     = 'd3,
              LOCKING         = 'd4,
              PLL_LOCKED      = 'd5,
              PRE_SWITCH      = 'd6,
              SWITCH_RESET    = 'd7,
              SWITCH_1        = 'd8,
              SWITCH_2        = 'd9;
              
              

wire          enable_ff2;
wire [1:0]    core_vco_sel_ff2;
reg  [3:0]    state, nstate;
reg  [7:0]    count, count_in;
reg  [1:0]    cur_vco_sel, cur_vco_sel_in;
reg           en_lock_det_in;
reg           en_fastlock_in;
reg           vctrl_locked_in;
reg           enable_fbclk_in;
reg           fastlock_ready_in;
reg           loss_of_lock_in;
reg           pll_reset_in;
wire          locked_ff2;
reg           switch_done_in;
reg           vco_gfcm_sel_in;
reg           vco1_en_in;
reg           vco2_en_in;

demet_reset u_demet_reset[3:0] (
  .clk     ( clk                    ),              
  .reset   ( reset                  ),              
  .sig_in  ( {core_vco_sel,
              locked,
              enable}               ),   
  .sig_out ( {core_vco_sel_ff2,
              locked_ff2,
              enable_ff2}           )); 




always @(posedge clk or posedge reset) begin
  if(reset) begin
    state               <= IDLE;
    count               <= 'd0;
    cur_vco_sel         <= 'd0;
    en_lock_det         <= 1'b0;
    en_fastlock         <= 1'b0;
    vctrl_locked        <= 1'b0;
    enable_fbclk        <= 1'b0;
    fastlock_ready      <= 1'b0;
    loss_of_lock        <= 1'b0;
    pll_reset           <= 1'b1;
    switch_done         <= 1'b0;
    vco_gfcm_sel        <= 1'b0;
    vco1_en             <= 1'b0;
    vco2_en             <= 1'b0;
  end else begin
    state               <= nstate;
    count               <= count_in;
    cur_vco_sel         <= cur_vco_sel_in;
    en_lock_det         <= en_lock_det_in;
    en_fastlock         <= en_fastlock_in;
    vctrl_locked        <= vctrl_locked_in;
    enable_fbclk        <= enable_fbclk_in;
    fastlock_ready      <= fastlock_ready_in;
    loss_of_lock        <= loss_of_lock_in;
    pll_reset           <= pll_reset_in;
    switch_done         <= switch_done_in;
    vco_gfcm_sel        <= vco_gfcm_sel_in;
    vco1_en             <= vco1_en_in;
    vco2_en             <= vco2_en_in;
  end
end

assign fsm_state = state;

always @(*) begin
  nstate                  = state;
  count_in                = 'd0;
  cur_vco_sel_in          = cur_vco_sel;
  en_lock_det_in          = en_lock_det;
  en_fastlock_in          = en_fastlock;
  vctrl_locked_in         = vctrl_locked;
  enable_fbclk_in         = enable_fbclk;
  fastlock_ready_in       = fastlock_ready;
  loss_of_lock_in         = 1'b0;
  pll_reset_in            = pll_reset;
  switch_done_in          = switch_done;
  vco_gfcm_sel_in         = vco_gfcm_sel;
  vco1_en_in              = vco1_en;
  vco2_en_in              = vco2_en;
  
  case(state)
    //---------------------------------
    IDLE : begin
      vctrl_locked_in     = 1'b0;
      enable_fbclk_in     = 1'b0;
      pll_reset_in        = 1'b1;
      vco1_en_in          = 1'b0;
      vco2_en_in          = 1'b0;
      if(enable_ff2) begin
        pll_reset_in      = 1'b0;
        enable_fbclk_in   = 1'b1;
        cur_vco_sel_in    = core_vco_sel_ff2;
        vco1_en_in        = core_vco_sel_ff2 == VCO1;
        vco2_en_in        = core_vco_sel_ff2 == VCO2;
        count_in          = 'd0;
        nstate            = BIAS_SETTLE;
      end
    end
    
    //---------------------------------
    BIAS_SETTLE : begin
      if(count == swi_bias_settle_count) begin
        count_in          = 'd0;
        en_lock_det_in    = 1'b1;
        en_fastlock_in    = 1'b1;
        nstate            = FASTLOCKING;
      end else begin
        count_in          = count + 'd1;
      end
      
      //for fast sims
      if ($test$plusargs("MVP_FORCE_PLL")) begin 
        switch_done_in    = 1'b0;
        nstate            = PLL_LOCKED;
      end  
    end
    
    //---------------------------------
    FASTLOCKING : begin
      if(locked_ff2) begin
        en_lock_det_in    = 1'b0;
        en_fastlock_in    = 1'b0;
        fastlock_ready_in = 1'b1;
        nstate            = PRE_LOCKING;
      end 
    end
    
    
    //---------------------------------
    //Switch to Normal lock settings
    PRE_LOCKING : begin
      en_lock_det_in      = 1'b0;
      if(count == swi_pre_locking_count) begin
        nstate            = LOCKING;
        en_lock_det_in    = 1'b1;
      end else begin
        count_in          = count + 'd1;
      end
    end
    
    //---------------------------------
    LOCKING : begin
      if(locked_ff2) begin
        switch_done_in    = 1'b0;
        nstate            = PLL_LOCKED;
      end 
      
      //for fast sims
      if ($test$plusargs("MVP_FORCE_PLL")) begin 
        switch_done_in    = 1'b0;
        nstate            = PLL_LOCKED;
      end      
    end
    
    
    //---------------------------------
    //Wait until VCO sel is changed
    PLL_LOCKED : begin
      en_lock_det_in      = ~swi_disable_lock_det_after_lock; //Save power bruddha
      vctrl_locked_in     = 1'b1;
      loss_of_lock_in     = ~locked_ff2;
      if(core_switch_vco) begin
        nstate            = PRE_SWITCH;
        switch_done_in    = 1'b0; 
        enable_fbclk_in   = 1'b0;       
        en_lock_det_in    = 1'b0;
        fastlock_ready_in = 1'b0;
      end
      
      //for fast sims (ignore loss of lock)
      if ($test$plusargs("MVP_FORCE_PLL")) begin 
        loss_of_lock_in   = 1'b0;
      end  
    end
    
    //---------------------------------
    //Disable the FBCLK gate here to prevent glitches on the clock during the change over
    PRE_SWITCH : begin
      //Enable the VCOs which need to be, and keep the current enabled
      vco1_en_in          = (core_vco_sel_ff2 == VCO1) || (cur_vco_sel == VCO1);
      vco2_en_in          = (core_vco_sel_ff2 == VCO2) || (cur_vco_sel == VCO2);
      if(count == swi_pre_switch_time) begin
        nstate            = SWITCH_RESET;
        pll_reset_in      = 1'b1;
        count_in          = 'd0;
      end else begin
        count_in          = count + 'd1;
      end
    end
    
    
    //---------------------------------
    SWITCH_RESET : begin
      pll_reset_in        = 1'b1;
      cur_vco_sel_in      = core_vco_sel_ff2;
      if(count == swi_switch_reset_time) begin
        pll_reset_in      = 1'b0;
        nstate            = SWITCH_1;
      end else begin
        count_in          = count + 'd1;
      end
    end
    
    
    //---------------------------------
    SWITCH_1 : begin
      pll_reset_in        = 1'b0;
      //vco_gfcm_sel_in     = cur_vco_sel == VCO2;
      if(count == swi_switch_1_time) begin
        vco_gfcm_sel_in   = cur_vco_sel == VCO2;
        count_in          = 'd0;
        nstate            = SWITCH_2;
      end else begin
        count_in          = count + 'd1;
      end
    end
    
    
    //---------------------------------
    SWITCH_2 : begin
      //Disable the VCO we are no longer using
      pll_reset_in        = 1'b0;
      //vco1_en_in          = (cur_vco_sel == VCO1);
      //vco2_en_in          = (cur_vco_sel == VCO2);
      if(count == swi_switch_2_time) begin
        vco1_en_in        = (cur_vco_sel == VCO1);
        vco2_en_in        = (cur_vco_sel == VCO2);
        en_lock_det_in    = 1'b1;
        enable_fbclk_in   = 1'b1;
        count_in          = 'd0;
        switch_done_in    = 1'b1; 
        nstate            = LOCKING;
      end else begin
        count_in          = count + 'd1;
      end
    end
    
    
    default : begin
      nstate              = IDLE;
    end
  endcase
end


assign vco_sel = cur_vco_sel;

assign ready   = (state == PLL_LOCKED);

endmodule
