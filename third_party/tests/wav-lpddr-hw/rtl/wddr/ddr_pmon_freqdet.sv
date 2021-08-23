
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

module ddr_pmon_freqdet ( refclk, pllclk, done, plllock_en, lockrefclkcount,
                          plllock_cmp, refclkreset, force_plllock, lockrange, reset_plllock,
                          pllclkreset, lockresult);

output reg [23:0] lockresult;
input pllclkreset;
input refclkreset;
input reset_plllock;
input [11:0] lockrefclkcount;
input [9:0] lockrange;
input plllock_en;
input refclk;
input pllclk;
input force_plllock;
input [23:0] plllock_cmp;
output reg done;

reg [15:0] refclkcount;
reg [23:0] pllclkcount;
wire [15:0] refclkcount_in;
wire startover_togin;
reg startover_tog;
wire startover_ff2;
reg startover_ff3;
wire compare;
wire [23:0] pllclkcount_in;
wire [19:0] pllcount_cmp_lut;
//wire [23:0] pllcount_cmp;
wire [23:0] pllcount_cmpp16;
wire [23:0] pllcount_cmpm16;
wire [23:0] pllcount_cmpp;
wire [23:0] pllcount_cmpm;
wire done_in;
reg done_pre ;
reg done_ff;
//wire equal;
wire plllock_enrefclkff2, plllock_enpllclkff2;
//wire reset_plllockff2;
//wire force_plllockff2;
wire [23:0] lockresult_in;
reg plllock_enpllclkff3;
wire done_pre_in;
wire done_ff_in;


  ddr_demet_r plllockenrefclksync 
         (.i_clk(refclk), 
          .i_rst(refclkreset), 
          .i_d(plllock_en), 
          .o_q(plllock_enrefclkff2));

  ddr_demet_r plllockenpllclksync 
         (.i_clk(pllclk), 
          .i_rst(pllclkreset), 
          .i_d(plllock_en), 
          .o_q(plllock_enpllclkff2));
//  demet_reset plllockresetsync (.clk(pllclk), .reset(pllclkreset), .sig_in(reset_plllock), .sig_out(reset_plllockff2));

  assign refclkcount_in = ((refclkcount == lockrefclkcount) | ~plllock_enrefclkff2) ? 16'h0000 : (refclkcount + 16'h0001);

  always @(posedge refclk or posedge refclkreset) begin
    if (refclkreset) begin
      refclkcount <= 16'hfff0;
    end else begin
      refclkcount <= refclkcount_in;
    end
  end

  assign startover_togin = (refclkcount_in == {4'h0, lockrefclkcount}) ? ~startover_tog : startover_tog;

  always @(posedge refclk or posedge refclkreset) begin
    if (refclkreset) begin
      startover_tog <= 1'b0;
    end else begin
      startover_tog <= startover_togin;
    end
  end

  ddr_demet_r startoverdemet 
         (.i_clk(pllclk), 
          .i_rst(pllclkreset), 
          .i_d(startover_tog), 
          .o_q(startover_ff2));

  always @(posedge pllclk or posedge pllclkreset) begin
      if (pllclkreset) begin
        startover_ff3 <= 1'b0;
      end else begin
        startover_ff3 <= startover_ff2;
      end
  end

  assign compare = (startover_ff2 ^ startover_ff3);
  assign pllclkcount_in = (~plllock_enpllclkff2 | compare) ? 24'h000000 : pllclkcount + 24'h000001;
  assign lockresult_in = compare & ~done ? pllclkcount : lockresult;

  always @(posedge pllclk or posedge pllclkreset) begin
    if (pllclkreset) begin
      pllclkcount <= 24'h000000;
      lockresult <= 24'h000000;
    end else begin
      pllclkcount <= pllclkcount_in;
      lockresult <= lockresult_in;
    end
  end

//  assign pllcount_cmp = plllock_cmp;
  assign pllcount_cmpp = plllock_cmp + {14'b00000000000000, lockrange};
  assign pllcount_cmpm = plllock_cmp - {14'b00000000000000, lockrange};

//  assign equal = (pllclkcount >= pllcount_cmpm) & (pllclkcount <= pllcount_cmpp);

  assign done_in = plllock_enpllclkff2 & ~plllock_enpllclkff3 ? 1'b0 : (done_ff ? 1'b1 : done);
  assign done_pre_in = plllock_enpllclkff2 & ~plllock_enpllclkff3 ? 1'b0 : (compare ? 1'b1 : done_pre);
  assign done_ff_in = plllock_enpllclkff2 & ~plllock_enpllclkff3 ? 1'b0 : (done_pre ? 1'b1 : done_ff);

//  demet_reset forceplllocksync (.clk(pllclk), .reset(pllclkreset), .sig_in(force_plllock), .sig_out(force_plllockff2));

  always @(posedge pllclk or posedge pllclkreset) begin
    if (pllclkreset) begin
      done_pre <= 1'b0;
      done_ff <= 1'b0;
      done <= 1'b0;
      plllock_enpllclkff3 <= 1'b0;
    end else begin
      done_pre <= done_pre_in;
      done_ff <= done_ff_in;
      done <= done_in;
      plllock_enpllclkff3 <= plllock_enpllclkff2 ;
    end
  end

endmodule
