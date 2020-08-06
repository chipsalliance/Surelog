// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

// This file is auto-generated.

`ifndef PRIM_DEFAULT_IMPL
  `define PRIM_DEFAULT_IMPL prim_pkg::ImplGeneric
`endif

module prim_rom

#(

  parameter  int Width       = 32,
  parameter  int Depth       = 2048, // 8kB default
  parameter      MemInitFile = "", // VMEM file to initialize the memory with

  localparam int Aw          = $clog2(Depth)

) (
  input  logic             clk_i,
  input  logic             req_i,
  input  logic [Aw-1:0]    addr_i,
  output logic [Width-1:0] rdata_o
);
  parameter prim_pkg::impl_e Impl = `PRIM_DEFAULT_IMPL;

  if (1) begin : gen_generic
    prim_generic_rom #(
      .Depth(Depth),
      .MemInitFile(MemInitFile),
      .Width(Width)
    ) u_impl_generic (
      .*
    );

  end

endmodule
