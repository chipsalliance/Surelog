// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

// Macros and helper code for using assertions.
//  - Provides default clk and rst options to simplify code
//  - Provides boiler plate template for common assertions

`ifndef PRIM_ASSERT_SV
`define PRIM_ASSERT_SV


///////////////////
// Helper macros //
///////////////////

// local helper macro to reduce code clutter. undefined at the end of this file
`ifndef VERILATOR
`ifndef SYNTHESIS
`define INC_ASSERT
`endif
`endif



// Assert a concurrent property directly.
// It can be called as a module (or interface) body item.
`define ASSERT(__name, __prop, __clk = cl, __rst = rs) \
`ifdef INC_ASSERT                                      \
                                                       \
`endif                                                 \

				       
				       
// Note: Above we use (__rst !== '0) in the disable iff statements instead of
// (__rst == '1).  This properly disables the assertion in cases when reset is X at
// the beginning of a simulation. For that case, (reset == '1) does not disable the
// assertion.


`endif // PRIM_ASSERT_SV
