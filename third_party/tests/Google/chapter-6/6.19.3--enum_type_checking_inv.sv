// Copyright (C) 2019-2021  The SymbiFlow Authors.
//
// Use of this source code is governed by a ISC-style
// license that can be found in the LICENSE file or at
// https://opensource.org/licenses/ISC
//
// SPDX-License-Identifier: ISC


/*
:name: enum_type_checking_inv
:description: invalid enum assignment tests
:should_fail_because: enum enforces strict type checking rules
:tags: 6.19.3
:type: simulation
*/
module top();
	typedef enum {a, b, c, d} e;

	initial begin
		e val;
		val = 1;
	end
endmodule
