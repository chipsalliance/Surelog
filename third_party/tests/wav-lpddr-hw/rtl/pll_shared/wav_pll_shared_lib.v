  
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

module pll_freq_detect #(
  parameter  REF_WIDTH   = 10,
  parameter  FB_WIDTH    = 10
)(
  input  wire                            ref_clk,
  input  wire                            ref_reset,
  input  wire                            fb_clk,
  input  wire                            fb_reset,
  input  wire                            enable,
  input  wire [5:0]                      range,
  input  wire [REF_WIDTH-1:0]            ref_cycles,
  input  wire [FB_WIDTH-1:0]             fb_target,         
  output reg  [FB_WIDTH-1:0]             fb_cycles,
  output reg                             match
);


wire                     enable_ref_ff2;
wire                     enable_fb_ff2;

wire [REF_WIDTH-1:0]     ref_cnt_in;
reg  [REF_WIDTH-1:0]     ref_cnt_ff;
wire                     ref_tog_in;
reg                      ref_tog_ff;

wire [FB_WIDTH-1:0]      fb_cnt_in;
reg  [FB_WIDTH-1:0]      fb_cnt_ff;
wire                     ref_tog_ff2;
reg                      ref_tog_ff3;
wire                     ref_toggled;

wire [FB_WIDTH:0]        fb_upper_target;
wire [FB_WIDTH:0]        fb_lower_target;
wire                     match_in;


assign fb_upper_target = fb_target + range[5:0];
assign fb_lower_target = {1'b0, fb_target - range[5:0]};
assign match_in = enable_fb_ff2  ? (ref_toggled ? ((({1'b0, fb_cnt_ff} >= fb_lower_target) && ({1'b0, fb_cnt_ff} <= fb_upper_target)) ? 1'b1 : 1'b0) : match) : 1'b0;

demet_reset u_demet_enable_ref(
  .clk      ( ref_clk              ),
  .reset    ( ref_reset            ),
  .sig_in   ( enable               ),
  .sig_out  ( enable_ref_ff2       ));

demet_reset u_demet_enable_fb(
  .clk      ( fb_clk               ),
  .reset    ( fb_reset             ),
  .sig_in   ( enable               ),
  .sig_out  ( enable_fb_ff2        ));

demet_reset u_demet_ref_tog(
  .clk      ( fb_clk               ),
  .reset    ( fb_reset             ),
  .sig_in   ( ref_tog_ff           ),
  .sig_out  ( ref_tog_ff2          ));

assign ref_cnt_in = enable_ref_ff2 ? (ref_cnt_ff == {REF_WIDTH{1'b0}}) ? ref_cycles : ref_cnt_ff - 1'b1 : ref_cycles;
assign ref_tog_in = (ref_cnt_ff == {REF_WIDTH{1'b0}}) ? ~ref_tog_ff : ref_tog_ff;

assign fb_cnt_in = enable_fb_ff2 ? ref_toggled ? {FB_WIDTH{1'b0}} : fb_cnt_ff + 1'b1 : {FB_WIDTH{1'b0}};
assign ref_toggled = ref_tog_ff3^ref_tog_ff2;

always @(posedge fb_clk or posedge fb_reset) begin
  if (fb_reset) begin
    fb_cnt_ff     <= {FB_WIDTH{1'b0}};
    ref_tog_ff3   <= 1'b0;
    fb_cycles     <= {FB_WIDTH{1'b0}};
    match         <= 1'b0;
  end else begin
    fb_cnt_ff     <= fb_cnt_in;
    ref_tog_ff3   <= ref_tog_ff2;
    fb_cycles     <= ref_toggled ? fb_cnt_ff : fb_cycles;
    match         <= match_in;
  end
end

always @(posedge ref_clk or posedge ref_reset) begin
  if (ref_reset) begin
    ref_cnt_ff    <= {REF_WIDTH{1'b0}};
    ref_tog_ff    <= 1'b0;
  end else begin
    ref_cnt_ff    <= ref_cnt_in;
    ref_tog_ff    <= ref_tog_in;
  end
end

endmodule




/*
.rst_start
SSC Generator
=============

The SSC Generator will create a Spread Spectrum Clocking modulation to feed the mash.
It does this by creating a triangle waveform with an offset based on the settings. 

There are three main settings for the SSC Generation (from a protocol perspective):
* SSC PPM - Amount of variance from the base clock frequency in terms of PPM
* SSC Freq - Frequency of the PPM variance (usually 30-33kHz)
* Center/Down Spread - Center would be +/- 1/2 PPM, while down would be -PPM only

For example, applying 5000PPM with 33kHz in downspread to a 5GHz clock, would result in
the output clock varying between 5GHz and 4.975GHz every 30.3us. If this were center spread
the clock would vary between 5.0125GHz and 4.9875GHz.

Configuring the SSC Generator involves programming the following settings

* Amplitude (``ssc_amp``)     - This is a factor of the PPM offset
* StepSize  (``ssc_stepsize``)- This in conjunction with the Amplitude will give you the SSC frequency component
* Center    (``ssc_center``)  - Denotes center vs. downspread

The formulas for these settings are as follows:

::
  
  ssc_amp       = ((ssc_ppm / 1e6) * VCO Freq) / (Feedback Clock Freq / 2^16) 
  ssc_stepsize  = ssc_amp / (Refclk Freq / (2 * SSC Freq))
  
  if(ssc_center){
    ssc_amp = ssc_amp / 2
  }
  
The amplitude is used to factor how much of the FracN component is required to meet your PPM. We then
take the calculated amplitude and divide it by how many steps it takes to get the SSC freq in terms
of RefClk Cycles.

.rst_end
*/
module pll_ssc #(
  parameter STEPSIZE_WIDTH  = 10,
  parameter AMPLITUDE_WIDTH = 17, // this should probably be removed and always be SSC_WIDTH-1
  parameter SSC_WIDTH       = 18
)(
  clk, 
  reset, 
  stepsize, 
  amplitude, 
  enable, 
  count_cycles, 
  centerspread, 
  sscout
);

input count_cycles;
input clk;
input reset;
input [STEPSIZE_WIDTH-1:0] stepsize;
input [AMPLITUDE_WIDTH-1:0] amplitude;
input enable;
input centerspread;
output [SSC_WIDTH-1:0] sscout;

wire [SSC_WIDTH-1:0] sscout_in;
reg [SSC_WIDTH-1:0] sscout;
wire switch;
wire [AMPLITUDE_WIDTH-1:0] direction_count_in;
reg [AMPLITUDE_WIDTH-1:0] direction_count;
reg direction;
wire direction_in;
wire center_in;
reg center;
wire change_direction;
wire [STEPSIZE_WIDTH-1:0] stepsize_mx;
wire top, bottom;
wire [SSC_WIDTH-1:0] sscmag;
wire sscsign;

wire enable_ff2;


demet_reset u_demet_reset (
  .clk    ( clk       ), 
  .reset  ( reset     ), 
  .sig_in ( enable    ), 
  .sig_out( enable_ff2));




assign sscsign = sscout[SSC_WIDTH-1];

assign sscmag = sscsign ? (~sscout + {{SSC_WIDTH-1{1'b0}}, 1'b1}) : sscout;

assign top = centerspread ? ~sscsign & ({1'b0, amplitude} <= sscout) : ~sscsign;

assign bottom = sscsign & (sscmag >= amplitude);

assign switch = count_cycles ? (direction_count == amplitude) : (direction ? top : bottom);

assign direction_count_in = (~enable_ff2 | switch) ? {AMPLITUDE_WIDTH{1'b0}} : direction_count + {AMPLITUDE_WIDTH{1'b1}};

always @(posedge clk or posedge reset) begin
  if (reset) begin
    direction_count <= {AMPLITUDE_WIDTH{1'b0}};
  end else begin
    direction_count <= direction_count_in;
  end
end

always @(posedge clk or posedge reset) begin
  if (reset) begin
    direction <= 1'b0;
  end else begin
    direction <= direction_in;
  end
end

assign center_in = switch & centerspread & count_cycles ? ~center : center;

always @(posedge clk or posedge reset) begin
  if (reset) begin
    center <= 1'b0;
  end else begin
    center <= center_in;
  end
end

assign change_direction = switch & enable_ff2 & (~count_cycles | ~center | ~centerspread);

assign direction_in = change_direction ? ~direction : direction;

assign stepsize_mx  = enable_ff2 ? stepsize : {STEPSIZE_WIDTH{1'b0}};

assign sscout_in = (change_direction ^ direction) ? sscout + stepsize_mx : sscout - stepsize_mx;

always @(posedge clk or posedge reset) begin
  if (reset) begin 
    sscout <= {SSC_WIDTH{1'b0}};
  end else begin
    sscout <= sscout_in;
  end
end

endmodule 




// -------------------------------------------------------------
// 
// File Name: hdlsrc\mash_hdl_tb\mash.v
// Created: 2017-09-27 05:08:55
// 
// Generated by MATLAB 9.0 and HDL Coder 3.8
// 
// 
// -- -------------------------------------------------------------
// -- Rate and Clocking Details
// -- -------------------------------------------------------------
// Model base rate: 2.60417e-08
// Target subsystem base rate: 2.60417e-08
// 
// 
// Clock Enable  Sample Time
// -- -------------------------------------------------------------
// ce_out        2.60417e-08
// -- -------------------------------------------------------------
// 
// 
// Output Signal                 Clock Enable  Sample Time
// -- -------------------------------------------------------------
// divout                        ce_out        2.60417e-08
// -- -------------------------------------------------------------
// 
// -------------------------------------------------------------


// -------------------------------------------------------------
// 
// Module: mash
// Source Path: mash_hdl_tb/mash
// Hierarchy Level: 0
// 
// -------------------------------------------------------------

`timescale 1 ns / 1 ns

module pll_mash
          (
           clk,
           reset,
           //clk_enable,
           frac,
           sscoffsetin,
           intg,
           frac_en,
           //ce_out,
           divout
          );


  input   clk;
  input   reset;
  //input   clk_enable;
  input   [15:0] frac;  // uint16
  input   signed [17:0] sscoffsetin;  // sfix18
  input   [8:0] intg;  // ufix9
  input   frac_en;
  //output  ce_out;
  output  [8:0] divout;  // ufix9


  //stevenb
  wire clk_enable;
  assign clk_enable = 1'b1;

  wire enb;
  wire switch_compare_1;
  wire [16:0] Data_Type_Conversion_out1;  // ufix17
  wire signed [18:0] Sum8_1;  // sfix19
  wire signed [18:0] Sum8_2;  // sfix19
  wire signed [18:0] Sum8_out1;  // sfix19
  wire signed [18:0] Shift_Arithmetic_out1;  // sfix19
  wire Constant_out1;
  wire signed [19:0] Sum6_1;  // sfix20
  wire signed [19:0] Sum6_2;  // sfix20
  wire signed [19:0] Sum6_out1;  // sfix20
  wire signed [18:0] Constant2_out1;  // sfix19_E2
  wire signed [20:0] Sum7_add_cast;  // sfix21
  wire signed [20:0] Sum7_1;  // sfix21
  wire signed [20:0] Sum7_out1;  // sfix21
  reg signed [20:0] Delay6_out1;  // sfix21
  wire [16:0] Extract_Bits7_out1;  // ufix17
  wire [20:0] Sum1_1;  // ufix21
  wire [20:0] Sum1_2;  // ufix21
  wire [20:0] Sum1_out1;  // ufix21
  reg [20:0] Delay_out1;  // ufix21
  wire [16:0] Extract_Bits1_out1;  // ufix17
  wire [17:0] Sum3_1;  // ufix18
  wire [17:0] Sum3_2;  // ufix18
  wire [17:0] Sum3_out1;  // ufix18
  reg [17:0] Delay1_out1;  // ufix18
  reg [17:0] Delay2_out1;  // ufix18
  wire [16:0] Extract_Bits4_out1;  // ufix17
  wire [17:0] Sum2_1;  // ufix18
  wire [17:0] Sum2_2;  // ufix18
  wire [17:0] Sum2_out1;  // ufix18
  wire Extract_Bits5_out1;  // ufix1
  reg  Delay4_out1;  // ufix1
  wire signed [2:0] Sum5_stage2_1;  // sfix3
  wire signed [2:0] Sum5_stage2_2;  // sfix3
  wire signed [2:0] Sum5_op_stage2;  // sfix3
  wire Extract_Bits3_out1;  // ufix1
  reg  Delay7_out1;  // ufix1
  wire signed [2:0] Sum5_stage3_1;  // sfix3
  wire signed [2:0] Sum5_out1;  // sfix3
  reg signed [2:0] Delay3_out1;  // sfix3
  wire signed [3:0] Sum4_stage2_1;  // sfix4
  wire signed [3:0] Sum4_stage2_2;  // sfix4
  wire signed [3:0] Sum4_op_stage2;  // sfix4
  wire [3:0] Extract_Bits_out1;  // ufix4
  reg [3:0] Delay8_reg [0:1];  // ufix4 [2]
  wire [3:0] Delay8_reg_next [0:1];  // ufix4 [2]
  wire [3:0] Delay8_out1;  // ufix4
  wire signed [3:0] Sum4_stage3_1;  // sfix4
  wire signed [3:0] Sum4_op_stage3;  // sfix4
  wire [1:0] Constant1_out1;  // ufix2
  wire signed [3:0] Sum4_stage4_1;  // sfix4
  wire signed [3:0] Sum4_out1;  // sfix4
  wire signed [9:0] Sum9_add_temp;  // sfix10
  wire signed [9:0] Sum9_1;  // sfix10
  wire signed [9:0] Sum9_2;  // sfix10
  wire [8:0] Sum9_out1;  // ufix9
  reg [8:0] Delay5_out1;  // ufix9
  wire [8:0] Switch_out1;  // ufix9


  assign switch_compare_1 = frac_en > 1'b0;



  assign Data_Type_Conversion_out1 = {1'b0, frac};



  assign Sum8_1 = {2'b0, Data_Type_Conversion_out1};
  assign Sum8_2 = {sscoffsetin[17], sscoffsetin};
  assign Sum8_out1 = Sum8_1 + Sum8_2;



  assign Shift_Arithmetic_out1 = Sum8_out1 <<< 8'd1;



  assign Constant_out1 = 1'b1;



  assign Sum6_1 = {Shift_Arithmetic_out1[18], Shift_Arithmetic_out1};
  assign Sum6_2 = {19'b0, Constant_out1};
  assign Sum6_out1 = Sum6_1 + Sum6_2;



  assign Constant2_out1 = 19'sb0010000000000000000;



  assign Sum7_add_cast = {Constant2_out1, 2'b00};
  assign Sum7_1 = {Sum6_out1[19], Sum6_out1};
  assign Sum7_out1 = Sum7_1 + Sum7_add_cast;



  assign enb = clk_enable;

  always @(posedge clk or posedge reset)
    begin : Delay6_process
      if (reset == 1'b1) begin
        Delay6_out1 <= 21'sb000000000000000000000;
      end
      else begin
        if (enb) begin
          Delay6_out1 <= Sum7_out1;
        end
      end
    end



  assign Sum1_1 = Delay6_out1;
  assign Sum1_2 = {4'b0, Extract_Bits7_out1};
  assign Sum1_out1 = Sum1_1 + Sum1_2;



  always @(posedge clk or posedge reset)
    begin : Delay_process
      if (reset == 1'b1) begin
        Delay_out1 <= 21'b000000000000000000000;
      end
      else begin
        if (enb) begin
          Delay_out1 <= Sum1_out1;
        end
      end
    end



  assign Extract_Bits7_out1 = Delay_out1[16:0];



  assign Sum3_1 = {1'b0, Extract_Bits7_out1};
  assign Sum3_2 = {1'b0, Extract_Bits1_out1};
  assign Sum3_out1 = Sum3_1 + Sum3_2;



  always @(posedge clk or posedge reset)
    begin : Delay1_process
      if (reset == 1'b1) begin
        Delay1_out1 <= 18'b000000000000000000;
      end
      else begin
        if (enb) begin
          Delay1_out1 <= Sum3_out1;
        end
      end
    end



  assign Extract_Bits1_out1 = Delay1_out1[16:0];



  assign Extract_Bits4_out1 = Delay2_out1[16:0];



  assign Sum2_1 = {1'b0, Extract_Bits1_out1};
  assign Sum2_2 = {1'b0, Extract_Bits4_out1};
  assign Sum2_out1 = Sum2_1 + Sum2_2;



  always @(posedge clk or posedge reset)
    begin : Delay2_process
      if (reset == 1'b1) begin
        Delay2_out1 <= 18'b000000000000000000;
      end
      else begin
        if (enb) begin
          Delay2_out1 <= Sum2_out1;
        end
      end
    end



  assign Extract_Bits5_out1 = Delay2_out1[17];



  always @(posedge clk or posedge reset)
    begin : Delay4_process
      if (reset == 1'b1) begin
        Delay4_out1 <= 1'b0;
      end
      else begin
        if (enb) begin
          Delay4_out1 <= Extract_Bits5_out1;
        end
      end
    end



  assign Sum5_stage2_1 = {2'b0, Extract_Bits5_out1};
  assign Sum5_stage2_2 = {2'b0, Delay4_out1};
  assign Sum5_op_stage2 = Sum5_stage2_1 - Sum5_stage2_2;



  assign Extract_Bits3_out1 = Delay1_out1[17];



  always @(posedge clk or posedge reset)
    begin : Delay7_process
      if (reset == 1'b1) begin
        Delay7_out1 <= 1'b0;
      end
      else begin
        if (enb) begin
          Delay7_out1 <= Extract_Bits3_out1;
        end
      end
    end



  assign Sum5_stage3_1 = {2'b0, Delay7_out1};
  assign Sum5_out1 = Sum5_op_stage2 + Sum5_stage3_1;



  always @(posedge clk or posedge reset)
    begin : Delay3_process
      if (reset == 1'b1) begin
        Delay3_out1 <= 3'sb000;
      end
      else begin
        if (enb) begin
          Delay3_out1 <= Sum5_out1;
        end
      end
    end



  assign Sum4_stage2_1 = {Sum5_out1[2], Sum5_out1};
  assign Sum4_stage2_2 = {Delay3_out1[2], Delay3_out1};
  assign Sum4_op_stage2 = Sum4_stage2_1 - Sum4_stage2_2;



  assign Extract_Bits_out1 = Delay_out1[20:17];



  always @(posedge clk or posedge reset)
    begin : Delay8_process
      if (reset == 1'b1) begin
        Delay8_reg[0] <= 4'b0000;
        Delay8_reg[1] <= 4'b0000;
      end
      else begin
        if (enb) begin
          Delay8_reg[0] <= Delay8_reg_next[0];
          Delay8_reg[1] <= Delay8_reg_next[1];
        end
      end
    end

  assign Delay8_out1 = Delay8_reg[1];
  assign Delay8_reg_next[0] = Extract_Bits_out1;
  assign Delay8_reg_next[1] = Delay8_reg[0];



  assign Sum4_stage3_1 = Delay8_out1;
  assign Sum4_op_stage3 = Sum4_op_stage2 + Sum4_stage3_1;



  assign Constant1_out1 = 2'b10;



  assign Sum4_stage4_1 = {2'b0, Constant1_out1};
  assign Sum4_out1 = Sum4_op_stage3 - Sum4_stage4_1;



  assign Sum9_1 = {1'b0, intg};
  assign Sum9_2 = {{6{Sum4_out1[3]}}, Sum4_out1};
  assign Sum9_add_temp = Sum9_1 + Sum9_2;
  assign Sum9_out1 = Sum9_add_temp[8:0];



  always @(posedge clk or posedge reset)
    begin : Delay5_process
      if (reset == 1'b1) begin
        Delay5_out1 <= 9'b000000000;
      end
      else begin
        if (enb) begin
          Delay5_out1 <= Sum9_out1;
        end
      end
    end
  
  reg frac_bypass_reg;
  always @(posedge clk or posedge reset) begin
    if(reset) begin
      frac_bypass_reg <= 1'b1;
    end else begin
      frac_bypass_reg <= 1'b0;
    end
  end


  assign Switch_out1 = (((switch_compare_1 == 1'b0) || frac_bypass_reg) && (~(|sscoffsetin)) ? intg :
              Delay5_out1);



  assign divout = Switch_out1;

  assign ce_out = clk_enable;

endmodule  // mash

