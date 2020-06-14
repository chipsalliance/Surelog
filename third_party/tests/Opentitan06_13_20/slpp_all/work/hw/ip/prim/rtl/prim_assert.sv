// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

// Macros and helper code for using assertions.
//  - Provides default clk and rst options to simplify code
//  - Provides boiler plate template for common assertions













///////////////////
// Helper macros //
///////////////////

// local helper macro to reduce code clutter. undefined at the end of this file






// Converts an arbitrary block of code into a Verilog string

// ASSERT_RPT is available to change the reporting mechanism when an assert fails

///////////////////////////////////////
// Simple assertion and cover macros //
///////////////////////////////////////

// Default clk and reset signals used by assertion macros below.

// Immediate assertion
// Note that immediate assertions are sensitive to simulation glitches.

// Assertion in initial block. Can be used for things like parameter checking.

// Assertion in final block. Can be used for things like queues being empty
// at end of sim, all credits returned at end of sim, state machines in idle
// at end of sim.

// Assert a concurrent property directly.
// It can be called as a module (or interface) body item.
// Note: Above we use (__rst !== '0) in the disable iff statements instead of
// (__rst == '1).  This properly disables the assertion in cases when reset is X at
// the beginning of a simulation. For that case, (reset == '1) does not disable the
// assertion.

// Assert a concurrent property NEVER happens

// Assert that signal has a known value (each bit is either '0' or '1') after reset.
// It can be called as a module (or interface) body item.

//  Cover a concurrent property

//////////////////////////////
// Complex assertion macros //
//////////////////////////////

// Assert that signal is an active-high pulse with pulse length of 1 clock cycle

// Assert that a property is true only when an enable signal is set.  It can be called as a module
// (or interface) body item.

// Assert that signal has a known value (each bit is either '0' or '1') after reset if enable is
// set.  It can be called as a module (or interface) body item.

///////////////////////
// Assumption macros //
///////////////////////

// Assume a concurrent property

// Assume an immediate property

//////////////////////////////////
// For formal verification only //
//////////////////////////////////

// Note that the existing set of ASSERT macros specified above shall be used for FPV,
// thereby ensuring that the assertions are evaluated during DV simulations as well.

// ASSUME_FPV
// Assume a concurrent property during formal verification only.

// ASSUME_I_FPV
// Assume a concurrent property during formal verification only.

// COVER_FPV
// Cover a concurrent property during formal verification

