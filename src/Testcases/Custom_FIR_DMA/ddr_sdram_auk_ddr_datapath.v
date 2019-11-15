//Legal Notice: (C)2010 Altera Corporation. All rights reserved.  Your
//use of Altera Corporation's design tools, logic functions and other
//software and tools, and its AMPP partner logic functions, and any
//output files any of the foregoing (including device programming or
//simulation files), and any associated documentation or information are
//expressly subject to the terms and conditions of the Altera Program
//License Subscription Agreement or other applicable license agreement,
//including, without limitation, that your use is for the sole purpose
//of programming logic devices manufactured by Altera and sold by Altera
//or its authorized distributors.  Please refer to the applicable
//agreement for further details.

// synthesis translate_off
`timescale 1ps / 1ps
// synthesis translate_on

// turn off superfluous verilog processor warnings 
// altera message_level Level1 
// altera message_off 10034 10035 10036 10037 10230 10240 10030 

module ddr_sdram_auk_ddr_datapath (
                                    // inputs:
                                     capture_clk,
                                     clk,
                                     control_be,
                                     control_doing_rd,
                                     control_doing_wr,
                                     control_dqs_burst,
                                     control_wdata,
                                     control_wdata_valid,
                                     dqs_delay_ctrl,
                                     dqsupdate,
                                     postamble_clk,
                                     reset_n,
                                     resynch_clk,
                                     write_clk,

                                    // outputs:
                                     clk_to_sdram,
                                     clk_to_sdram_n,
                                     control_rdata,
                                     ddr_dm,
                                     ddr_dq,
                                     ddr_dqs
                                  )
;

  parameter gstratixii_dqs_phase = 6000;
  parameter gstratixii_dqs_out_mode = "delay_chain2";
  parameter gstratixii_dll_delay_buffer_mode = "low";


  output           clk_to_sdram;
  output           clk_to_sdram_n;
  output  [ 31: 0] control_rdata;
  output  [  1: 0] ddr_dm;
  inout   [ 15: 0] ddr_dq;
  inout   [  1: 0] ddr_dqs;
  input            capture_clk;
  input            clk;
  input   [  3: 0] control_be;
  input            control_doing_rd;
  input            control_doing_wr;
  input            control_dqs_burst;
  input   [ 31: 0] control_wdata;
  input            control_wdata_valid;
  input   [  5: 0] dqs_delay_ctrl;
  input            dqsupdate;
  input            postamble_clk;
  input            reset_n;
  input            resynch_clk;
  input            write_clk;

  wire    [  3: 0] be_temp;
  wire             capture_clk_int;
  wire             clk_to_sdram;
  wire             clk_to_sdram_n;
  wire    [ 31: 0] control_rdata;
  wire    [  1: 0] ddr_dm;
  wire    [ 15: 0] ddr_dq;
  wire    [  1: 0] ddr_dqs;
  wire             postamble_clk_int;
  wire    [ 31: 0] rdata_temp;
  wire             resynch_clk_int;
  wire    [ 31: 0] wdata_temp;
  wire             write_clk_int;
  //
  //************************
  // Clock generator module 
  ddr_sdram_auk_ddr_clk_gen ddr_clk_gen
    (
      .clk (clk),
      .clk_to_sdram (clk_to_sdram),
      .clk_to_sdram_n (clk_to_sdram_n),
      .reset_n (reset_n)
    );


  //
  //**********************************
  // DQS group instantiation for dqs[0] 
  assign wdata_temp[15 : 0] = {control_wdata[23 : 16],control_wdata[7 : 0]};
  assign control_rdata[23 : 16] = rdata_temp[15 : 8];
  assign control_rdata[7 : 0] = rdata_temp[7 : 0];
  assign be_temp[1 : 0] = {control_be[2], control_be[0]};
  ddr_sdram_auk_ddr_dqs_group \g_datapath:0:g_ddr_io 
    (
      .capture_clk (capture_clk_int),
      .clk (clk),
      .control_be (be_temp[1 : 0]),
      .control_doing_rd (control_doing_rd),
      .control_doing_wr (control_doing_wr),
      .control_dqs_burst (control_dqs_burst),
      .control_rdata (rdata_temp[15 : 0]),
      .control_wdata (wdata_temp[15 : 0]),
      .control_wdata_valid (control_wdata_valid),
      .ddr_dm (ddr_dm[0]),
      .ddr_dq (ddr_dq[7 : 0]),
      .ddr_dqs (ddr_dqs[0]),
      .dqs_delay_ctrl (dqs_delay_ctrl),
      .dqsupdate (dqsupdate),
      .postamble_clk (postamble_clk_int),
      .reset_n (reset_n),
      .resynch_clk (resynch_clk_int),
      .write_clk (write_clk_int)
    );

  defparam \g_datapath:0:g_ddr_io .gDLL_INPUT_FREQUENCY = "10000ps",
           \g_datapath:0:g_ddr_io .gSTRATIXII_DLL_DELAY_BUFFER_MODE = "low",
           \g_datapath:0:g_ddr_io .gSTRATIXII_DQS_OUT_MODE = "delay_chain2";

  //
  //**********************************
  // DQS group instantiation for dqs[1] 
  assign wdata_temp[31 : 16] = {control_wdata[31 : 24],control_wdata[15 : 8]};
  assign control_rdata[31 : 24] = rdata_temp[31 : 24];
  assign control_rdata[15 : 8] = rdata_temp[23 : 16];
  assign be_temp[3 : 2] = {control_be[3], control_be[1]};
  ddr_sdram_auk_ddr_dqs_group \g_datapath:1:g_ddr_io 
    (
      .capture_clk (capture_clk_int),
      .clk (clk),
      .control_be (be_temp[3 : 2]),
      .control_doing_rd (control_doing_rd),
      .control_doing_wr (control_doing_wr),
      .control_dqs_burst (control_dqs_burst),
      .control_rdata (rdata_temp[31 : 16]),
      .control_wdata (wdata_temp[31 : 16]),
      .control_wdata_valid (control_wdata_valid),
      .ddr_dm (ddr_dm[1]),
      .ddr_dq (ddr_dq[15 : 8]),
      .ddr_dqs (ddr_dqs[1]),
      .dqs_delay_ctrl (dqs_delay_ctrl),
      .dqsupdate (dqsupdate),
      .postamble_clk (postamble_clk_int),
      .reset_n (reset_n),
      .resynch_clk (resynch_clk_int),
      .write_clk (write_clk_int)
    );

  defparam \g_datapath:1:g_ddr_io .gDLL_INPUT_FREQUENCY = "10000ps",
           \g_datapath:1:g_ddr_io .gSTRATIXII_DLL_DELAY_BUFFER_MODE = "low",
           \g_datapath:1:g_ddr_io .gSTRATIXII_DQS_OUT_MODE = "delay_chain2";


//synthesis translate_off
//////////////// SIMULATION-ONLY CONTENTS
  assign #2500 write_clk_int = ~clk;
  assign resynch_clk_int = resynch_clk;
  assign postamble_clk_int = postamble_clk;
  assign capture_clk_int = capture_clk;

//////////////// END SIMULATION-ONLY CONTENTS

//synthesis translate_on
//synthesis read_comments_as_HDL on
//  assign write_clk_int = write_clk;
//  assign resynch_clk_int = resynch_clk;
//  assign postamble_clk_int = postamble_clk;
//  assign capture_clk_int = capture_clk;
//synthesis read_comments_as_HDL off

endmodule

