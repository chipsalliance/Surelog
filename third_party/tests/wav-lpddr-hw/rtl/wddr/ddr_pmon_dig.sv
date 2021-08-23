
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

module ddr_pmon_dig (input core_scan_asyncrst_ctrl,
                     input core_scan_mode,
                     input core_scan_in,
                     input core_scan_shift,
                     input core_scan_clk,
                     output core_scan_out,

                     input i_pmon_nand_clk,
                     input i_pmon_nor_clk,
                     input i_pmon_en_nor,
                     input i_pmon_en_nand,
                     input i_refclk,
                     input i_refclk_rst,
                     input [7:0] i_initwait,
                     input [11:0] i_pmon_refcount_nor,
                     input [11:0] i_pmon_refcount_nand,
                     output o_pmon_done_nor,
                     output o_pmon_done_nand,
                     output [23:0] o_pmon_count_nor,
                     output [23:0] o_pmon_count_nand
                     //output o_ana_nand_en,
                     //output o_ana_nor_en
                     );

wire ana_en;
wire refclk_sync, refclk_rst_sync;
wire [8:0] initcount_int;
reg [8:0] count;
reg pmon_en_nand_dig;
reg pmon_en_nor_dig;
wire pmon_en_nand_ff2;
wire pmon_en_nor_ff2;
reg pmon_int_rst;
wire nand_fout;
wire nor_fout;
wire nand_fout_rst;
wire nor_fout_rst;
//wire tielo;

//ddr_wcm_tielo u_tielo_0
//         (.o_z(tielo));

ddr_mux u_mux_pmon_nand
         (.i_a(i_pmon_nand_clk),
          .i_b(core_scan_clk),
          .i_sel(core_scan_mode),
          .o_z(nand_fout));

ddr_mux u_mux_pmon_nor
         (.i_a(i_pmon_nor_clk),
          .i_b(core_scan_clk),
          .i_sel(core_scan_mode),
          .o_z(nor_fout));

ddr_latch_s u_pmonrstnandsync
         (.i_clk(nor_fout),
          .i_set(pmon_int_rst),
          .i_d(1'b0),
          .o_q(nor_fout_rst));

ddr_latch_s u_pmonrstnorsync
         (.i_clk(nand_fout),
          .i_set(pmon_int_rst),
          .i_d(1'b0),
          .o_q(nand_fout_rst));

ddr_mux u_refclkmux
         (.i_a(i_refclk),
          .i_b(core_scan_clk),
          .i_sel(core_scan_mode),
          .o_z(refclk_sync));

ddr_latch_s u_refclksync
         (.i_clk(i_refclk),
          .i_set(i_refclk_rst),
          .i_d(1'b0),
          .o_q(refclk_rst_sync));

//ddr_wcm_demet u_refclksync
//         (.i_clk(i_refclk),
//          .i_clk_b(refclk_b),
//          .i_d(i_refclk_rst),
//          .o_q(refclk_rst_sync));

ddr_demet_r u_enablenandrst
         (.i_clk(refclk_sync),
          .i_rst(refclk_rst_sync),
          .i_d(i_pmon_en_nand),
          .o_q(pmon_en_nand_ff2));

ddr_demet_r u_enablenorrst
         (.i_clk(refclk_sync),
          .i_rst(refclk_rst_sync),
          .i_d(i_pmon_en_nor),
          .o_q(pmon_en_nor_ff2));

assign ana_en = pmon_en_nand_ff2 | pmon_en_nor_ff2;
assign o_ana_nand_en = pmon_en_nand_ff2;
assign o_ana_nor_en = pmon_en_nor_ff2;

assign initcount_int = i_initwait == 8'h00 |
                       i_initwait == 8'h01 |
                       i_initwait == 8'h02 |
                       i_initwait == 8'h03 |
                       i_initwait == 8'h04 |
                       i_initwait == 8'h05 ? 9'h006 : {1'b0, i_initwait};

always @(posedge refclk_sync or posedge refclk_rst_sync)  begin
  if (refclk_rst_sync) begin
    count <= 9'h000;
    pmon_en_nand_dig <= 1'b0;
    pmon_en_nor_dig <= 1'b0;
    pmon_int_rst <= 1'b1;
  end else begin
    count <= ~ana_en ? 9'h000 : ((count == initcount_int) ? count : count + 9'h001);
    pmon_en_nand_dig <= count == initcount_int ? pmon_en_nand_ff2 : 1'b0;
    pmon_en_nor_dig <= count == initcount_int ? pmon_en_nor_ff2 : 1'b0;
    pmon_int_rst <= count == 9'h003 ? 1'b0 : (~ana_en ? 1'b1 : pmon_int_rst);
  end
end

ddr_pmon_freqdet pmon_freqdet_nor
         (.pllclk(nor_fout),  // process monitor out
          .pllclkreset(nor_fout_rst),
          .refclk(refclk_sync),
          .refclkreset(refclk_rst_sync),
          .done(o_pmon_done_nor),
          .plllock_en(pmon_en_nor_dig),
          .lockrefclkcount(i_pmon_refcount_nor),
          .plllock_cmp(24'h000000),
          .force_plllock(1'b0),
          .lockrange(10'b00_0100_0000),
          .reset_plllock(1'b0),
          .lockresult(o_pmon_count_nor));

ddr_pmon_freqdet pmon_freqdet_nand
         (.pllclk(nand_fout),  // process monitor out
          .pllclkreset(nand_fout_rst),
          .refclk(refclk_sync),
          .refclkreset(refclk_rst_sync),
          .done(o_pmon_done_nand),
          .plllock_en(pmon_en_nand_dig),
          .lockrefclkcount(i_pmon_refcount_nand),
          .plllock_cmp(24'h000000),
          .force_plllock(1'b0),
          .lockrange(10'b00_0100_0000),
          .reset_plllock(1'b0),
          .lockresult(o_pmon_count_nand));

endmodule
