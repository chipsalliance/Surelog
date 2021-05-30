// Copyright (C) 2019-2021  The SymbiFlow Authors.
//
// Use of this source code is governed by a ISC-style
// license that can be found in the LICENSE file or at
// https://opensource.org/licenses/ISC
//
// SPDX-License-Identifier: ISC


/*
:name: proc_assignment__bad
:description: continuous assignment with delay test
:should_fail_because: Illegal to procedurally assign to wire, IEEE Table 10-1
:tags: 10.3
:type: simulation
*/
module top(input a, input b);

wire w;

// Illegal to procedurally assign to wire, IEEE Table 10-1
initial
	w = #10 a & b;

endmodule
