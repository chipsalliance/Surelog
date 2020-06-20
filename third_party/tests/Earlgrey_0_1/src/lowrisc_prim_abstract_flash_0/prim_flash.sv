// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

// This file is auto-generated.

`ifndef PRIM_DEFAULT_IMPL
  `define PRIM_DEFAULT_IMPL prim_pkg::ImplGeneric
`endif

module prim_flash

#(

  parameter int PagesPerBank = 256, // pages per bank
  parameter int WordsPerPage = 256, // words per page
  parameter int DataWidth   = 32,   // bits per word
  parameter bit SkipInit = 1,       // this is an option to reset flash to all F's at reset

  // Derived parameters
  localparam int PageW = $clog2(PagesPerBank),
  localparam int WordW = $clog2(WordsPerPage),
  localparam int AddrW = PageW + WordW

) (
  input                        clk_i,
  input                        rst_ni,
  input                        rd_i,
  input                        prog_i,
  input                        pg_erase_i,
  input                        bk_erase_i,
  input [AddrW-1:0]            addr_i,
  input [DataWidth-1:0]        prog_data_i,
  output logic                 ack_o,
  output logic [DataWidth-1:0] rd_data_o,
  output logic                 init_busy_o
);
  parameter prim_pkg::impl_e Impl = `PRIM_DEFAULT_IMPL;

  if (1) begin : gen_generic
    prim_generic_flash #(
      .WordsPerPage(WordsPerPage),
      .PagesPerBank(PagesPerBank),
      .SkipInit(SkipInit),
      .DataWidth(DataWidth)
    ) u_impl_generic (
      .*
    );

  end

endmodule
