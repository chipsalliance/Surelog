// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0
//
// Description: UART top level wrapper file

// `include "prim_assert.sv"

module uart_top (
    input  clk_i,
    input  rst_ni,

  // Bus Interface
    input  tlul_pkg::tl_h2d_t tl_i,
    output tlul_pkg::tl_d2h_t tl_o,
   
    output tx_o,
    input  rx_i,
    
    output intr_tx
);
    
    logic [31:0] wdata;
    logic [31:0] addr;
    logic        we;
    logic        re;
    logic        rdata;
    logic [3:0]  be;
    
uart_core u_uart_core(
    .clk_i   (clk_i),
    .rst_ni  (rst_ni),
    
    .ren     (re),
    .we      (we),
    .wdata   (wdata),
    .rdata   (rdata),
    .addr    (addr),    
    .tx_o    (tx_o),
    .rx_i    (rx_i),
    
    .intr_tx (intr_tx)
);

    
 tlul_adapter_reg #(
    .RegAw(4),
    .RegDw(32)
 ) u_reg_if (
   .clk_i,
   .rst_ni,
    
   .tl_i (tl_i),
   .tl_o (tl_o),
    
   .we_o    (we),
   .re_o    (re),
   .addr_o  (addr),
   .wdata_o (wdata),
   .be_o    (be),
   .rdata_i (rdata),
   .error_i (1'b0)
);
endmodule
