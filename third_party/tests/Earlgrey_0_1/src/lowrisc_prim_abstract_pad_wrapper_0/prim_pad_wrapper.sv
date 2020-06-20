// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

// This file is auto-generated.

`ifndef PRIM_DEFAULT_IMPL
  `define PRIM_DEFAULT_IMPL prim_pkg::ImplGeneric
`endif

module prim_pad_wrapper

#(

  parameter int unsigned AttrDw = 6

) (
  inout wire         inout_io, // bidirectional pad
  output logic       in_o,     // input data
  input              out_i,    // output data
  input              oe_i,     // output enable
  // additional attributes {drive strength, keeper, pull-up, pull-down, open-drain, invert}
  input [AttrDw-1:0] attr_i
);
  parameter prim_pkg::impl_e Impl = `PRIM_DEFAULT_IMPL;

if (Impl == prim_pkg::ImplXilinx) begin : gen_xilinx
    prim_xilinx_pad_wrapper #(
      .AttrDw(AttrDw)
    ) u_impl_xilinx (
      .*
    );
end else begin : gen_generic
    prim_generic_pad_wrapper #(
      .AttrDw(AttrDw)
    ) u_impl_generic (
      .*
    );
end

endmodule
