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

module mvp_fll #(
  parameter       VCO_COUNT_WIDTH     = 16,
  parameter       REF_COUNT_WIDTH     = 8,
  parameter       RANGE_WIDTH         = 5
)(
  input  wire                         refclk,
  input  wire                         refclk_reset,
  
  input  wire                         vco_clk,
  input  wire                         vco_clk_reset,
  
  input  wire                         enable,
  input  wire                         swi_manual_mode,
  input  wire [REF_COUNT_WIDTH-1:0]   swi_ref_count,
  input  wire [VCO_COUNT_WIDTH-1:0]   swi_vco_count_target,
  input  wire [RANGE_WIDTH-1:0]       swi_range,
  input  wire [3:0]                   swi_delay_count,
  input  wire                         swi_use_demeted_check,
  input  wire [3:0]                   swi_locked_count_threshold,
  input  wire [5:0]                   swi_vco_band_start,
  input  wire [5:0]                   swi_vco_fine_start,
  input  wire [3:0]                   swi_fll_initial_settle,
  input  wire [5:0]                   swi_fll_band_thresh,
  input  wire                         swi_bypass_band,
  input  wire                         swi_bypass_fine,
  input  wire                         swi_persistent_mode,
  
  output wire                         fll_band_thresh_hit,
  output reg                          en_vco,
  output reg                          en_clk,
  output wire                         vco_too_fast_status,
  output wire                         vco_too_slow_status,
  output reg  [5:0]                   vco_band_prev,
  output wire [5:0]                   vco_band,
  
  
  output reg  [5:0]                   vco_fine_prev,
  output wire [5:0]                   vco_fine,
  
  
  output wire [VCO_COUNT_WIDTH-1:0]   vco_count_status,
  output wire                         locked
);

localparam  IDLE          = 'd0,
            SETTLE        = 'd1,
            COUNT         = 'd2,
            DELAY         = 'd3,
            FINE_DELAY    = 'd4,
            MANUAL_CHECK  = 'd5,
            FLL_LOCKED        = 'd6,
            CLK_EXIT      = 'd7;


wire                        enable_ff2;       
wire                        enable_vco_count; 

reg  [REF_COUNT_WIDTH-1:0]  refclk_count;
reg  [REF_COUNT_WIDTH-1:0]  refclk_count_in;
reg  [VCO_COUNT_WIDTH-1:0]  vco_count;
wire [VCO_COUNT_WIDTH-1:0]  vco_count_in;

reg [2:0]                   state, nstate;
reg                         en_counters, en_counters_in;

reg  [5:0]                  vco_band_reg, vco_band_reg_in;
reg  [5:0]                  vco_band_prev_in;
wire [5:0]                  vco_band_reg_p1;
wire [5:0]                  vco_band_reg_m1;

reg                         run_fine_cal, run_fine_cal_in;
reg  [5:0]                  vco_fine_reg, vco_fine_reg_in;
reg  [5:0]                  vco_fine_prev_in;
wire [5:0]                  vco_fine_reg_p1;
wire [5:0]                  vco_fine_reg_m1;

wire [VCO_COUNT_WIDTH:0]    vco_lower_bound;
wire [VCO_COUNT_WIDTH:0]    vco_upper_bound;
wire                        vco_too_slow;          
wire                        vco_too_fast;
wire                        vco_too_slow_refclk;          
wire                        vco_too_fast_refclk;

reg                         enable_vco_count_prev;
wire                        reset_vco_count;

reg  [3:0]                  locked_count, locked_count_in;
reg                         incr_lock_count;

reg                         en_vco_in;
reg                         en_clk_in;
reg                         enable_ff3;
wire                        enable_falling_edge;

demet_reset u_demet_reset_refclk[2:0] (
  .clk     ( refclk                   ),              
  .reset   ( refclk_reset             ),              
  .sig_in  ( {enable,
              vco_too_slow,
              vco_too_fast}           ),   
  .sig_out ( {enable_ff2,
              vco_too_slow_refclk,
              vco_too_fast_refclk}    )); 


demet_reset u_demet_reset_vco_clk (
  .clk     ( vco_clk                  ),              
  .reset   ( vco_clk_reset            ),              
  .sig_in  ( {en_counters}            ),   
  .sig_out ( {enable_vco_count}       )); 


always @(posedge refclk or posedge refclk_reset) begin
  if(refclk_reset) begin
    state             <= IDLE;
    refclk_count      <= 'd0;
    en_counters       <= 1'b0;
    vco_band_reg      <= 'd0;
    vco_band_prev     <= 'd0;
    vco_fine_reg      <= 'd31;
    vco_fine_prev     <= 'd0;
    locked_count      <= 'd0;
    en_vco            <= 1'b0;
    en_clk            <= 1'b0;
    enable_ff3        <= 1'b0;
    run_fine_cal      <= 1'b0;
  end else begin
    state             <= nstate;
    refclk_count      <= refclk_count_in;
    en_counters       <= en_counters_in;
    vco_band_reg      <= vco_band_reg_in;
    vco_band_prev     <= vco_band_prev_in;
    vco_fine_reg      <= vco_fine_reg_in;
    vco_fine_prev     <= vco_fine_prev_in;
    locked_count      <= locked_count_in;
    en_vco            <= en_vco_in;
    en_clk            <= en_clk_in;
    enable_ff3        <= enable_ff2;
    run_fine_cal      <= run_fine_cal_in;
  end
end

assign enable_falling_edge = enable_ff3 & ~enable_ff2;


assign vco_band_reg_p1     = vco_band_reg == 6'h3f ? vco_band_reg : vco_band_reg + 'd1;
assign vco_band_reg_m1     = vco_band_reg == 6'h00 ? vco_band_reg : vco_band_reg - 'd1;

assign vco_band            = vco_band_reg;
assign fll_band_thresh_hit = vco_band >= swi_fll_band_thresh;

assign vco_fine_reg_p1     = vco_fine_reg == 6'h3f ? vco_fine_reg : vco_fine_reg + 'd1;
assign vco_fine_reg_m1     = vco_fine_reg == 6'h00 ? vco_fine_reg : vco_fine_reg - 'd1;

assign vco_fine             = vco_fine_reg;

assign vco_too_fast_status = vco_too_fast_refclk;
assign vco_too_slow_status = vco_too_slow_refclk;

//assign locked              = locked_count >= swi_locked_count_threshold;
assign locked              = state == FLL_LOCKED;

//Keep up with vco_band to see if toggling. Band should always be toggling +/-1
//prev is essentially N-2 on the update cycle, so just look to see if the next one
//is +/-1 from prev

always @(*) begin
  nstate                  = state;
  en_counters_in          = 1'b0;
  refclk_count_in         = refclk_count;
  vco_band_reg_in         = vco_band_reg;
  vco_band_prev_in        = vco_band_prev;
  vco_fine_reg_in         = vco_fine_reg;
  vco_fine_prev_in        = vco_fine_prev;
  locked_count_in         = locked_count;
  incr_lock_count         = 1'b0;
  en_vco_in               = en_vco;
  en_clk_in               = en_clk;
  run_fine_cal_in         = run_fine_cal;
  
  case(state)
    //--------------------------------------
    IDLE : begin
      locked_count_in     = 'd0;
      en_vco_in           = 1'b0;
      en_clk_in           = 1'b0;
      refclk_count_in     = 'd0;
      run_fine_cal_in     = 1'b0;
      if(enable_ff2) begin
        en_vco_in         = 1'b1;
        //en_counters_in    = 1'b1;
        nstate            = SETTLE;
        vco_band_reg_in   = swi_vco_band_start;
        vco_fine_reg_in   = swi_vco_fine_start; 
        run_fine_cal_in   = swi_bypass_band;
      end
    end
    
    //--------------------------------------
    //Wait here for VCO to come up and settle
    SETTLE : begin
      if(refclk_count == {{REF_COUNT_WIDTH-4{1'b0}}, swi_fll_initial_settle}) begin
        en_counters_in    = 1'b1;
        refclk_count_in   = 'd0;
        en_clk_in         = 1'b1;
        nstate            = COUNT;
      end else begin
        refclk_count_in   = refclk_count + 'd1;
      end
    end
    
    //--------------------------------------
    //Enable refclk and vco clock counters
    COUNT : begin
      if(refclk_count == swi_ref_count) begin
        refclk_count_in   = {{REF_COUNT_WIDTH-4{1'b0}}, swi_delay_count};
        en_counters_in    = 1'b0;
        nstate            = swi_manual_mode ? MANUAL_CHECK : 
                            run_fine_cal    ? FINE_DELAY   : DELAY;
      end else begin
        en_counters_in    = 1'b1;
        refclk_count_in   = refclk_count + 'd1;
      end
    end
    
    //--------------------------------------
    //Delay for vco count to stop and read stable status
    DELAY : begin
      if(refclk_count == {REF_COUNT_WIDTH{1'b0}}) begin
        refclk_count_in   = 'd0;
        vco_band_prev_in  = vco_band_reg;
        
        //In Silicon we can try to not use the demetted version
        if(swi_use_demeted_check) begin
          case({vco_too_fast_refclk, vco_too_slow_refclk})
            2'b01   : vco_band_reg_in = vco_band_reg_p1;
            2'b10   : vco_band_reg_in = vco_band_reg_m1;
            default : vco_band_reg_in = vco_band_reg;
          endcase
        end else begin
          case({vco_too_fast, vco_too_slow})
            2'b01   : vco_band_reg_in = vco_band_reg_p1;
            2'b10   : vco_band_reg_in = vco_band_reg_m1;
            default : vco_band_reg_in = vco_band_reg;
          endcase
        end
        
        //Increment lock count
        if((vco_band_reg_in != vco_band_prev      ) && 
           (vco_band_reg_in != vco_band_prev + 'd1) && 
           (vco_band_reg_in != vco_band_prev - 'd1)) begin
          incr_lock_count = 1'b0;
        end else begin
          incr_lock_count = 1'b1;
        end
        locked_count_in   = incr_lock_count ? ((locked_count == 4'hf) ? locked_count : locked_count + 'd1) : 'd0; 
        
        if((locked_count_in >= swi_locked_count_threshold) && ~(swi_persistent_mode && swi_bypass_fine)) begin
          nstate          = swi_bypass_fine ? FLL_LOCKED : SETTLE;
          run_fine_cal_in = swi_bypass_fine ? 1'b0   : 1'b1;
          locked_count_in = 'd0;  //can this work?
        end else begin
          nstate          = SETTLE;
        end
        
        en_counters_in    = 1'b0;
        //nstate            = SETTLE; //Go back to settle for freq adj
      end else begin
        refclk_count_in   = refclk_count - 'd1;
      end
    end
    
    //--------------------------------------
    FINE_DELAY : begin
      if(refclk_count == {REF_COUNT_WIDTH{1'b0}}) begin
        refclk_count_in   = 'd0;
        vco_fine_prev_in  = vco_fine_reg;
        
        //In Silicon we can try to not use the demetted version
        if(swi_use_demeted_check) begin
          case({vco_too_fast_refclk, vco_too_slow_refclk})
            2'b01   : vco_fine_reg_in = vco_fine_reg_p1;
            2'b10   : vco_fine_reg_in = vco_fine_reg_m1;
            default : vco_fine_reg_in = vco_fine_reg;
          endcase
        end else begin
          case({vco_too_fast, vco_too_slow})
            2'b01   : vco_fine_reg_in = vco_fine_reg_p1;
            2'b10   : vco_fine_reg_in = vco_fine_reg_m1;
            default : vco_fine_reg_in = vco_fine_reg;
          endcase
        end
        
        //Increment lock count
        if((vco_fine_reg_in != vco_fine_prev      ) && 
           (vco_fine_reg_in != vco_fine_prev + 'd1) && 
           (vco_fine_reg_in != vco_fine_prev - 'd1)) begin
          incr_lock_count = 1'b0;
        end else begin
          incr_lock_count = 1'b1;
        end
        locked_count_in   = incr_lock_count ? ((locked_count == 4'hf) ? locked_count : locked_count + 'd1) : 'd0; 
        
        if((locked_count_in >= swi_locked_count_threshold) && ~swi_persistent_mode) begin
          nstate          = FLL_LOCKED;
          run_fine_cal_in = 1'b0;
        end else begin
          nstate          = SETTLE;
        end
        
        
        en_counters_in    = 1'b0;
        //nstate            = SETTLE; //Go back to settle for freq adj
      end else begin
        refclk_count_in   = refclk_count - 'd1;
      end
    end
    
    //--------------------------------------
    //If the locked_count is equal to setting, we will just come here and wait
    FLL_LOCKED : begin
      if(~enable_ff2) begin
        nstate            = IDLE;
      end
    end
    
    //--------------------------------------
    //If doing all of the checks through SW, basically go to this 
    //state and wait for the next iteration
    MANUAL_CHECK : begin
      if(~enable_ff2) begin
        nstate          = IDLE;
        vco_band_reg_in = vco_band_reg;
        refclk_count_in = 'd0;
        en_counters_in  = 1'b0;
      end
    end
    
    //--------------------------------------
    //Small state to just gracefully disable the clock
    CLK_EXIT : begin
      nstate            = IDLE;
      en_vco_in         = 1'b0;
    end
  
  
    default : begin
      nstate        = IDLE;
    end
  endcase
  
  if(enable_falling_edge) begin
    nstate          = CLK_EXIT;
    vco_band_reg_in = vco_band_reg;
    refclk_count_in = 'd0;
    en_counters_in  = 1'b0;
    en_clk_in       = 1'b0;
  end
end




assign reset_vco_count  = enable_vco_count & ~enable_vco_count_prev;
assign vco_count_in     = reset_vco_count ? 'd0 : enable_vco_count ? (vco_count == {VCO_COUNT_WIDTH{1'b1}} ? vco_count : vco_count + 'd1) : vco_count;

assign vco_lower_bound  = swi_vco_count_target - swi_range;
assign vco_upper_bound  = swi_vco_count_target + swi_range;
assign vco_too_slow     = {1'b0, vco_count} < vco_lower_bound;
assign vco_too_fast     = {1'b0, vco_count} > vco_upper_bound;

assign vco_count_status = vco_count;

always @(posedge vco_clk or posedge vco_clk_reset) begin
  if(vco_clk_reset) begin
    vco_count                   <= 'd0;
    enable_vco_count_prev       <= 1'b0;
  end else begin
    vco_count                   <= vco_count_in;
    enable_vco_count_prev       <= enable_vco_count;
  end
end


endmodule


