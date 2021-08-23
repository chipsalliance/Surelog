
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

`include "ddr_global_define.vh"

import ddr_global_pkg::*;

module ddr_snoop #(
   parameter       PWIDTH     = 32,       // Pattern Width
   parameter       AHB_DWIDTH = 32,       // AHB data width
   parameter       EG_DEPTH   = 16,       // Egress FIFO depth
   parameter       TSWIDTH    = 16,       // TS Width
   parameter [0:0] RAM_MODEL  = 1'b0      // Enable RAM model
) (

   input  logic                     i_clk,
   input  logic                     i_rst,

   // Scan
   input  logic                     i_scan_mode,
   input  logic                     i_scan_rst_ctrl,
   input  logic                     i_scan_cgc_ctrl,

   input  logic                     i_snoop_mode,

   input  logic                     i_ts_enable,
   input  logic                     i_ts_reset,

   input  logic [PWIDTH-1:0]        i_data,

   input  logic                     i_pattern_0_en,
   input  logic                     i_pattern_0_polarity,
   input  logic [1:0]               i_pattern_0_mode,
   input  logic [PWIDTH-1:0]        i_pattern_0_val,
   output logic                     o_pattern_0_detect,

   input  logic                     i_pattern_1_en,
   input  logic                     i_pattern_1_polarity,
   input  logic [1:0]               i_pattern_1_mode,
   input  logic [PWIDTH-1:0]        i_pattern_1_val,
   output logic                     o_pattern_1_detect,

   input  logic                     i_eg_rdata_clr,
   input  logic                     i_eg_rdata_upd,
   output logic [AHB_DWIDTH-1:0]    o_eg_rdata,
   output logic                     o_eg_empty,
   output logic                     o_eg_full

);

   // ------------------------------------------------------------------------
   // Local Clock Gating
   // ------------------------------------------------------------------------
   logic clk_g, snoop_mode_sync;

   ddr_demet_r u_demet_sm    (.i_clk(i_clk), .i_rst(i_rst), .i_d(i_snoop_mode), .o_q(snoop_mode_sync));
   ddr_cgc_rl u_cgc_dfi_clk  (.i_clk(i_clk), .i_clk_en(snoop_mode_sync), .i_cgc_en(i_scan_cgc_ctrl), .o_clk(clk_g));

   // ------------------------------------------------------------------------
   // Timestamp Counter
   // ------------------------------------------------------------------------

   logic [TSWIDTH-1:0] timestamp_q;
   logic ts_enable_sync;
   logic ts_reset_sync;

   // Synchronize CSR controls
   ddr_demet_r u_demet_tse (.i_clk(clk_g), .i_rst(i_rst), .i_d(i_ts_enable), .o_q(ts_enable_sync));
   ddr_demet_r u_demet_tsr (.i_clk(clk_g), .i_rst(i_rst), .i_d(i_ts_reset ), .o_q(ts_reset_sync ));

   // Timestamp counter
   always_ff @ (posedge clk_g, posedge i_rst) begin
      if (i_rst)
         timestamp_q <= '0;
      else if (ts_reset_sync)
         timestamp_q <= '0;
      else if (ts_enable_sync)
         timestamp_q <= timestamp_q + 'd1;
   end

   // ------------------------------------------------------------------------
   // Pattern Checker 0
   // ------------------------------------------------------------------------

   logic pattern_0_en_sync;
   ddr_demet_r u_demet_pe_0 (.i_clk(i_clk), .i_rst(i_rst), .i_d(i_pattern_0_en), .o_q(pattern_0_en_sync));

   logic pattern_0_check;
   // Pattern check based on configuration
   assign pattern_0_check = pattern_0_en_sync & (
                               i_pattern_0_polarity ^ (
                                  i_pattern_0_mode == 2'b00 ? i_data == i_pattern_0_val :
                                  i_pattern_0_mode == 2'b01 ? i_data  > i_pattern_0_val :
                                  i_pattern_0_mode == 2'b10 ? i_data  < i_pattern_0_val :
                                  i_pattern_0_polarity
                               )
                            );

   logic pattern_0_check_q;
   always_ff @ (posedge clk_g, posedge i_rst)
      if (i_rst)
         pattern_0_check_q <= '0;
      else
         pattern_0_check_q <= pattern_0_check;

   assign o_pattern_0_detect = pattern_0_check_q;

   // ------------------------------------------------------------------------
   // Pattern Checker 1
   // ------------------------------------------------------------------------

   logic pattern_1_en_sync;
   ddr_demet_r u_demet_pe_1 (.i_clk(i_clk), .i_rst(i_rst), .i_d(i_pattern_1_en), .o_q(pattern_1_en_sync));

   logic pattern_1_check;
   // Pattern check based on configuration
   assign pattern_1_check = pattern_1_en_sync & (
                               i_pattern_1_polarity ^ (
                                  i_pattern_1_mode == 2'b00 ? i_data == i_pattern_1_val :
                                  i_pattern_1_mode == 2'b01 ? i_data  > i_pattern_1_val :
                                  i_pattern_1_mode == 2'b10 ? i_data  < i_pattern_1_val :
                                  i_pattern_1_polarity
                               )
                            );

   logic pattern_1_check_q;
   always_ff @ (posedge clk_g, posedge i_rst)
      if (i_rst)
         pattern_1_check_q <= '0;
      else
         pattern_1_check_q <= pattern_1_check;

   assign o_pattern_1_detect = pattern_1_check_q;

   // ------------------------------------------------------------------------
   // Buffer Egress - From Datapath
   // ------------------------------------------------------------------------

   localparam EG_WIDTH = TSWIDTH + 2;

   logic [EG_WIDTH-1:0] eg_wdata, eg_rdata;
   logic eg_write, eg_read, eg_empty_n ;
   logic eg_rdata_upd_sync, eg_rdata_upd_q;
   logic rdata_loader_upd;
   logic [EG_WIDTH-1:0] rdata_loader_q;

   // Read Data
   assign eg_wdata = {
      timestamp_q,
      pattern_1_check_q,
      pattern_0_check_q
   };

   assign eg_write   = (
      pattern_1_check_q |
      pattern_0_check_q
   );
   assign o_eg_empty =  ~eg_empty_n ;

   ddr_fifo #(
      .WWIDTH                       (EG_WIDTH),
      .RWIDTH                       (EG_WIDTH),
      .DEPTH                        (EG_DEPTH),
      .SYNC                         (1'b1),
      .RAM_MODEL                    (RAM_MODEL)
   ) u_eg_fifo (
      .i_scan_mode                  (i_scan_mode),
      .i_scan_rst_ctrl              (i_scan_rst_ctrl),
      .i_scan_cgc_ctrl              (i_scan_cgc_ctrl),
      .i_clr                        (i_eg_rdata_clr),
      .i_loop_mode                  ('0),
      .i_load_ptr                   ('0),
      .i_stop_ptr                   ('0),
      .i_start_ptr                  ('0),
      .i_wclk                       (clk_g),
      .i_wrst                       (i_rst),
      .i_write                      (eg_write),
      .i_wdata                      (eg_wdata),
      .o_early_full                 (/*OPEN*/),
      .o_full                       (o_eg_full),
      .i_rclk                       (clk_g),
      .i_rrst                       (i_rst),
      .i_read                       (eg_read),
      .o_rdata                      (eg_rdata),
      .o_early_empty_n              (/*OPEN*/),
      .o_empty_n                    (eg_empty_n)
   );

   // Synchronize CSR controls
   ddr_demet_r u_demet_ru (.i_clk(clk_g), .i_rst(i_rst), .i_d(i_eg_rdata_upd), .o_q(eg_rdata_upd_sync));

   always_ff @ (posedge clk_g, posedge i_rst) begin
      if (i_rst) begin
         eg_rdata_upd_q <= '0;
      end else begin
         eg_rdata_upd_q <= eg_rdata_upd_sync;
      end
   end

   // Update the data loader on a CSR toggle
   assign rdata_loader_upd =  eg_rdata_upd_q ^ eg_rdata_upd_sync;

   // Egress Write Data Loader
   always_ff @ (posedge clk_g, posedge i_rst) begin
      if (i_rst)
         rdata_loader_q <= '0;
      else if (rdata_loader_upd)
         rdata_loader_q <= eg_rdata;
   end

   // Pop read data from Egress FIFO
   assign eg_read = rdata_loader_upd;

   // Read data to CSR
   assign o_eg_rdata = {{AHB_DWIDTH-EG_WIDTH{1'b0}}, rdata_loader_q};

endmodule
