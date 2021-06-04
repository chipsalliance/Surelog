//`timescale 1ns/1ps
// Copyright lowRISC contributors.
// Copyright 2018 ETH Zurich and University of Bologna, see also CREDITS.md.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

/**
 * RISC-V register file
 *
 * Register file with 31 or 15x 32 bit wide registers. Register 0 is fixed to 0.
 * This register file is based on flip flops. Use this register file when
 * targeting FPGA synthesis or Verilator simulation.
 */

module brq_fp_register_file_ff #(
    parameter brq_pkg::rvfloat_e RVF       = brq_pkg::RV32FSingle,
    parameter int unsigned       DataWidth = 32
    ) (
    // Clock and Reset
    input  logic                 clk_i,
    input  logic                 rst_ni,

    //Read port R1
    input  logic [4:0]           raddr_a_i,
    output logic [DataWidth-1:0] rdata_a_o,

    //Read port R2
    input  logic [4:0]           raddr_b_i,
    output logic [DataWidth-1:0] rdata_b_o,

    //Read port R2
    input  logic [4:0]           raddr_c_i,
    output logic [DataWidth-1:0] rdata_c_o,


    // Write port W1
    input  logic [4:0]           waddr_a_i,
    input  logic [DataWidth-1:0] wdata_a_i,
    input  logic                 we_a_i

);
import brq_pkg::rvfloat_e;

  localparam int unsigned ADDR_WIDTH = (RVF==brq_pkg::RV64FDouble) ? 6 : 5;
  localparam int unsigned NUM_WORDS  = (RVF==brq_pkg::RV64FDouble) ? 64 : 32;

  logic [NUM_WORDS-1:0][DataWidth-1:0] rf_reg;
  logic [NUM_WORDS-1:0][DataWidth-1:0] rf_reg_q;
  logic [NUM_WORDS-1:0]                we_a_dec;

  always_comb begin : we_a_decoder
    for (int unsigned i = 0; i < NUM_WORDS; i++) begin
      we_a_dec[i] = (waddr_a_i == 5'(i)) ?  we_a_i : 1'b0;
    end
  end

  for (genvar i = 0; i < NUM_WORDS; i++) begin : g_rf_flops
    always_ff @(posedge clk_i or negedge rst_ni) begin
      if (!rst_ni) begin
        rf_reg_q[i] <= '0;
      end else if(we_a_dec[i]) begin
        rf_reg_q[i] <= wdata_a_i;
      end
//      else begin
//        rf_reg_q[5] <= 32'h41a00000;
//        rf_reg_q[6] <= 32'h41200000;
//      end
    end
  end

  assign rf_reg[NUM_WORDS-1:0] = rf_reg_q[NUM_WORDS-1:0];

  assign rdata_a_o = rf_reg[raddr_a_i];
  assign rdata_b_o = rf_reg[raddr_b_i];
  assign rdata_c_o = rf_reg[raddr_c_i];

endmodule
