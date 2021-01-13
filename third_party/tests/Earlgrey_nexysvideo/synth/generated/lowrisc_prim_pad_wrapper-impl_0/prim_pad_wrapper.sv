// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

// This file is auto-generated.

`ifndef PRIM_DEFAULT_IMPL
  `define PRIM_DEFAULT_IMPL prim_pkg::ImplGeneric
`endif

// This is to prevent AscentLint warnings in the generated
// abstract prim wrapper. These warnings occur due to the .*
// use. TODO: we may want to move these inline waivers
// into a separate, generated waiver file for consistency.
//ri lint_check_off OUTPUT_NOT_DRIVEN INPUT_NOT_READ
module prim_pad_wrapper

#(

  parameter int Variant  =  0, // currently ignored
  parameter int AttrDw   = 10,
  parameter bit WarlOnly =  0  // If set to 1, no pad is instantiated and only warl_o is driven

) (
  inout wire         inout_io, // bidirectional pad
  output logic       in_o,     // input data
  input              ie_i,     // input enable
  input              out_i,    // output data
  input              oe_i,     // output enable
  // additional attributes
  input        [AttrDw-1:0] attr_i,
  output logic [AttrDw-1:0] warl_o
);
  parameter prim_pkg::impl_e Impl = `PRIM_DEFAULT_IMPL;

if (Impl == prim_pkg::ImplXilinx) begin : gen_xilinx
    prim_xilinx_pad_wrapper #(
      .AttrDw(AttrDw),
      .WarlOnly(WarlOnly),
      .Variant(Variant)
    ) u_impl_xilinx (
      .*
    );
end else begin : gen_generic
    prim_generic_pad_wrapper #(
      .AttrDw(AttrDw),
      .WarlOnly(WarlOnly),
      .Variant(Variant)
    ) u_impl_generic (
      .*
    );
end

endmodule
//ri lint_check_on OUTPUT_NOT_DRIVEN INPUT_NOT_READ
