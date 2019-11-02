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

module ddr_sdram_auk_ddr_sdram (
                                 // inputs:
                                  addrcmd_clk,
                                  capture_clk,
                                  clk,
                                  dqs_delay_ctrl,
                                  dqsupdate,
                                  local_addr,
                                  local_autopch_req,
                                  local_be,
                                  local_burstbegin,
                                  local_read_req,
                                  local_refresh_req,
                                  local_size,
                                  local_wdata,
                                  local_write_req,
                                  mem_bl,
                                  mem_btype,
                                  mem_dll_en,
                                  mem_drv_str,
                                  mem_odt,
                                  mem_tcl,
                                  mem_tinit_time,
                                  mem_tmrd,
                                  mem_tras,
                                  mem_trcd,
                                  mem_trefi,
                                  mem_trfc,
                                  mem_trp,
                                  mem_twr,
                                  mem_twtr,
                                  postamble_clk,
                                  reset_n,
                                  resynch_clk,
                                  write_clk,

                                 // outputs:
                                  clk_to_sdram,
                                  clk_to_sdram_n,
                                  ddr_a,
                                  ddr_ba,
                                  ddr_cas_n,
                                  ddr_cke,
                                  ddr_cs_n,
                                  ddr_dm,
                                  ddr_dq,
                                  ddr_dqs,
                                  ddr_odt,
                                  ddr_ras_n,
                                  ddr_we_n,
                                  local_init_done,
                                  local_rdata,
                                  local_rdata_valid,
                                  local_rdvalid_in_n,
                                  local_ready,
                                  local_refresh_ack,
                                  local_wdata_req,
                                  stratix_dll_control
                               )
;

  parameter gFAMILY = "Stratix";
  parameter gSTRATIX_DLL_CONTROL = "false";
  parameter gPIPELINE_COMMANDS = "true";
  parameter gSTRATIXII_DQS_OUT_MODE = "delay_chain2";
  parameter gINTER_RESYNCH = "false";
  parameter gEXTRA_PIPELINE_REGS = "false";
  parameter gADDR_CMD_NEGEDGE = "false";
  parameter gSTRATIXII_DQS_PHASE = 6000;
  parameter gREG_DIMM = "false";
  parameter gSTRATIXII_DLL_DELAY_BUFFER_MODE = "low";
  parameter gUSER_REFRESH = "false";
  parameter gMEM_TYPE = "ddr_sdram";
  parameter gPIPELINE_READDATA = "true";
  parameter gLOCAL_AVALON_IF = "false";


  output           clk_to_sdram;
  output           clk_to_sdram_n;
  output  [ 12: 0] ddr_a;
  output  [  1: 0] ddr_ba;
  output           ddr_cas_n;
  output           ddr_cke;
  output           ddr_cs_n;
  output  [  1: 0] ddr_dm;
  inout   [ 15: 0] ddr_dq;
  inout   [  1: 0] ddr_dqs;
  output           ddr_odt;
  output           ddr_ras_n;
  output           ddr_we_n;
  output           local_init_done;
  output  [ 31: 0] local_rdata;
  output           local_rdata_valid;
  output           local_rdvalid_in_n;
  output           local_ready;
  output           local_refresh_ack;
  output           local_wdata_req;
  output           stratix_dll_control;
  input            addrcmd_clk;
  input            capture_clk;
  input            clk;
  input   [  5: 0] dqs_delay_ctrl;
  input            dqsupdate;
  input   [ 22: 0] local_addr;
  input            local_autopch_req;
  input   [  3: 0] local_be;
  input            local_burstbegin;
  input            local_read_req;
  input            local_refresh_req;
  input   [  2: 0] local_size;
  input   [ 31: 0] local_wdata;
  input            local_write_req;
  input   [  2: 0] mem_bl;
  input            mem_btype;
  input            mem_dll_en;
  input            mem_drv_str;
  input   [  1: 0] mem_odt;
  input   [  2: 0] mem_tcl;
  input   [ 15: 0] mem_tinit_time;
  input   [  1: 0] mem_tmrd;
  input   [  3: 0] mem_tras;
  input   [  2: 0] mem_trcd;
  input   [ 15: 0] mem_trefi;
  input   [  6: 0] mem_trfc;
  input   [  2: 0] mem_trp;
  input   [  2: 0] mem_twr;
  input   [  1: 0] mem_twtr;
  input            postamble_clk;
  input            reset_n;
  input            resynch_clk;
  input            write_clk;

  wire             clk_to_sdram;
  wire             clk_to_sdram_n;
  wire    [  3: 0] control_be;
  wire             control_doing_rd;
  wire             control_doing_wr;
  wire             control_dqs_burst;
  wire    [ 31: 0] control_rdata;
  wire    [ 31: 0] control_wdata;
  wire             control_wdata_valid;
  wire    [ 12: 0] ddr_a;
  wire    [  1: 0] ddr_ba;
  wire             ddr_cas_n;
  wire             ddr_cke;
  wire             ddr_cs_n;
  wire    [  1: 0] ddr_dm;
  wire    [ 15: 0] ddr_dq;
  wire    [  1: 0] ddr_dqs;
  wire             ddr_odt;
  wire             ddr_ras_n;
  wire             ddr_we_n;
  wire    [  1: 0] local_bank_addr;
  wire    [  7: 0] local_col_addr;
  wire             local_cs_addr;
  wire             local_init_done;
  wire    [ 31: 0] local_rdata;
  wire             local_rdata_valid;
  wire             local_rdvalid_in_n;
  wire             local_ready;
  wire             local_refresh_ack;
  wire    [ 12: 0] local_row_addr;
  wire             local_wdata_req;
  wire             stratix_dll_control;
  wire    [ 12: 0] tmp_ddr_a;
  wire    [  1: 0] tmp_ddr_ba;
  wire             tmp_ddr_cas_n;
  wire             tmp_ddr_cke;
  wire             tmp_ddr_cs_n;
  wire             tmp_ddr_odt;
  wire             tmp_ddr_ras_n;
  wire             tmp_ddr_we_n;
  assign local_cs_addr = 0;
  //


  assign local_bank_addr = local_addr[22 : 21];

  assign local_row_addr = local_addr[20 : 8];
  assign local_col_addr = local_addr[7 : 0];
  //-----------------------------------------------------------------------------
  //Controller
  //-----------------------------------------------------------------------------
  auk_ddr_controller ddr_control
    (
      .clk (clk),
      .control_be (control_be),
      .control_doing_rd (control_doing_rd),
      .control_doing_wr (control_doing_wr),
      .control_dqs_burst (control_dqs_burst),
      .control_rdata (control_rdata),
      .control_wdata (control_wdata),
      .control_wdata_valid (control_wdata_valid),
      .ddr_a (tmp_ddr_a),
      .ddr_ba (tmp_ddr_ba),
      .ddr_cas_n (tmp_ddr_cas_n),
      .ddr_cke (tmp_ddr_cke),
      .ddr_cs_n (tmp_ddr_cs_n),
      .ddr_odt (tmp_ddr_odt),
      .ddr_ras_n (tmp_ddr_ras_n),
      .ddr_we_n (tmp_ddr_we_n),
      .local_autopch_req (local_autopch_req),
      .local_bank_addr (local_bank_addr),
      .local_be (local_be),
      .local_burstbegin (local_burstbegin),
      .local_col_addr (local_col_addr),
      .local_cs_addr (local_cs_addr),
      .local_init_done (local_init_done),
      .local_rdata (local_rdata),
      .local_rdata_valid (local_rdata_valid),
      .local_rdvalid_in_n (local_rdvalid_in_n),
      .local_read_req (local_read_req),
      .local_ready (local_ready),
      .local_refresh_ack (local_refresh_ack),
      .local_refresh_req (local_refresh_req),
      .local_row_addr (local_row_addr),
      .local_size (local_size[2 : 0]),
      .local_wdata (local_wdata),
      .local_wdata_req (local_wdata_req),
      .local_write_req (local_write_req),
      .mem_bl (mem_bl),
      .mem_btype (mem_btype),
      .mem_dll_en (mem_dll_en),
      .mem_drv_str (mem_drv_str),
      .mem_odt (mem_odt),
      .mem_tcl (mem_tcl),
      .mem_tinit_time (mem_tinit_time),
      .mem_tmrd (mem_tmrd),
      .mem_tras (mem_tras),
      .mem_trcd (mem_trcd),
      .mem_trefi (mem_trefi),
      .mem_trfc (mem_trfc),
      .mem_trp (mem_trp),
      .mem_twr (mem_twr),
      .mem_twtr (mem_twtr),
      .reset_n (reset_n),
      .stratix_dll_control (stratix_dll_control),
      .write_clk (write_clk)
    );

  defparam ddr_control.gADDR_CMD_NEGEDGE = gADDR_CMD_NEGEDGE,
           ddr_control.gEXTRA_PIPELINE_REGS = gEXTRA_PIPELINE_REGS,
           ddr_control.gFAMILY = gFAMILY,
           ddr_control.gINTER_RESYNCH = gINTER_RESYNCH,
           ddr_control.gLOCAL_AVALON_IF = gLOCAL_AVALON_IF,
           ddr_control.gLOCAL_BURST_LEN = 4,
           ddr_control.gLOCAL_BURST_LEN_BITS = 3,
           ddr_control.gLOCAL_DATA_BITS = 32,
           ddr_control.gMEM_BANK_BITS = 2,
           ddr_control.gMEM_CHIPSELS = 1,
           ddr_control.gMEM_CHIP_BITS = 0,
           ddr_control.gMEM_COL_BITS = 9,
           ddr_control.gMEM_DQ_PER_DQS = 8,
           ddr_control.gMEM_ODT_RANKS = 0,
           ddr_control.gMEM_PCH_BIT = 10,
           ddr_control.gMEM_ROW_BITS = 13,
           ddr_control.gMEM_TYPE = gMEM_TYPE,
           ddr_control.gPIPELINE_COMMANDS = gPIPELINE_COMMANDS,
           ddr_control.gPIPELINE_READDATA = gPIPELINE_READDATA,
           ddr_control.gREG_DIMM = gREG_DIMM,
           ddr_control.gRESYNCH_CYCLE = 1,
           ddr_control.gSTRATIX_DLL_CONTROL = gSTRATIX_DLL_CONTROL,
           ddr_control.gUSER_REFRESH = gUSER_REFRESH;

  ddr_sdram_auk_ddr_datapath ddr_io
    (
      .capture_clk (capture_clk),
      .clk (clk),
      .clk_to_sdram (clk_to_sdram),
      .clk_to_sdram_n (clk_to_sdram_n),
      .control_be (control_be),
      .control_doing_rd (control_doing_rd),
      .control_doing_wr (control_doing_wr),
      .control_dqs_burst (control_dqs_burst),
      .control_rdata (control_rdata),
      .control_wdata (control_wdata),
      .control_wdata_valid (control_wdata_valid),
      .ddr_dm (ddr_dm[1 : 0]),
      .ddr_dq (ddr_dq),
      .ddr_dqs (ddr_dqs[1 : 0]),
      .dqs_delay_ctrl (dqs_delay_ctrl),
      .dqsupdate (dqsupdate),
      .postamble_clk (postamble_clk),
      .reset_n (reset_n),
      .resynch_clk (resynch_clk),
      .write_clk (write_clk)
    );

  defparam ddr_io.gstratixii_dll_delay_buffer_mode = gSTRATIXII_DLL_DELAY_BUFFER_MODE,
           ddr_io.gstratixii_dqs_out_mode = gSTRATIXII_DQS_OUT_MODE,
           ddr_io.gstratixii_dqs_phase = 6000;

  assign ddr_cs_n = tmp_ddr_cs_n;
  assign ddr_cke = tmp_ddr_cke;
  assign ddr_odt = tmp_ddr_odt;
  assign ddr_a = tmp_ddr_a;
  assign ddr_ba = tmp_ddr_ba;
  assign ddr_ras_n = tmp_ddr_ras_n;
  assign ddr_cas_n = tmp_ddr_cas_n;
  assign ddr_we_n = tmp_ddr_we_n;

endmodule

