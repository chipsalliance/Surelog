// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

// This file is auto-generated.

`ifndef PRIM_DEFAULT_IMPL
  `define PRIM_DEFAULT_IMPL prim_pkg::ImplGeneric
`endif

module prim_clock_gating

#(

) (
  input        clk_i,
  input        en_i,
  input        test_en_i,
  output logic clk_o
);
  parameter prim_pkg::impl_e Impl = `PRIM_DEFAULT_IMPL;

if (Impl == prim_pkg::ImplXilinx) begin : gen_xilinx
    prim_xilinx_clock_gating u_impl_xilinx (
      .*
    );
end else begin : gen_generic
    prim_generic_clock_gating u_impl_generic (
      .*
    );
end

endmodule
