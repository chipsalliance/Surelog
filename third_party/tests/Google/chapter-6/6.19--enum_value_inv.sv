// Copyright (C) 2019-2021  The SymbiFlow Authors.
//
// Use of this source code is governed by a ISC-style
// license that can be found in the LICENSE file or at
// https://opensource.org/licenses/ISC
//
// SPDX-License-Identifier: ISC


/*
:name: enum_value_inv
:description: Tests that tools diagnose invalid enum value assignments
:should_fail_because: If the integer value expression is a sized literal constant, it shall be an error if the size is different from the enum base type, even if the value is within the representable range.
:tags: 6.19
:runner_verilator_flags: -Werror-WIDTH
:type: simulation
*/
module top();
	// 6.19 says:
	// If the integer value expression is a sized literal constant, it shall
	// be an error if the size is different from the enum base type, even if
	// the value is within the representable range.
	enum logic [2:0] {
	  Global = 4'h2,
	  Local = 4'h3
	} myenum;
endmodule
