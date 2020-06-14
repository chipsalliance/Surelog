// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0
//
// Generic, technology independent pad wrapper. This is NOT synthesizable!


// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

// Macros and helper code for using assertions.
//  - Provides default clk and rst options to simplify code
//  - Provides boiler plate template for common assertions












































































































































module prim_generic_pad_wrapper #(
  parameter int unsigned AttrDw = 6
) (
  inout wire         inout_io, // bidirectional pad
  output logic       in_o,     // input data
  input              out_i,    // output data
  input              oe_i,     // output enable
  // additional attributes {drive strength, keeper, pull-up, pull-down, open-drain, invert}
  input [AttrDw-1:0] attr_i
);

  // get pad attributes
  logic kp, pu, pd, od, inv;
  typedef enum logic {STRONG_DRIVE = 1'b0, WEAK_DRIVE = 1'b1} drv_e;
  drv_e drv;
  assign {drv, kp, pu, pd, od, inv} = attr_i[5:0];

  // input inversion
  assign in_o     = inv ^ inout_io;

  // virtual open drain emulation
  logic oe, out;
  assign out      = out_i ^ inv;
  assign oe       = oe_i & ((od & ~out) | ~od);

// driving strength attributes are not supported by verilator



  // different driver types
  assign (strong0, strong1) inout_io = (oe && drv == STRONG_DRIVE) ? out : 1'bz;
  assign (pull0, pull1)     inout_io = (oe && drv == WEAK_DRIVE)   ? out : 1'bz;
  // pullup / pulldown termination
  // default to high-Z in case both PU and PD are asserted (safety mechanism).
  assign (highz0, weak1)    inout_io = pu & ~pd;
  assign (weak0, highz1)    inout_io = pu | ~pd;
  // fake trireg emulation
  assign (weak0, weak1)     inout_io = (kp) ? inout_io : 1'bz;


  // assertions
  

endmodule : prim_generic_pad_wrapper
