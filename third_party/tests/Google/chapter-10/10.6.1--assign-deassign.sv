// Copyright (C) 2019-2021  The SymbiFlow Authors.
//
// Use of this source code is governed by a ISC-style
// license that can be found in the LICENSE file or at
// https://opensource.org/licenses/ISC
//
// SPDX-License-Identifier: ISC


/*
:name: assign_deassign
:description: assign-deassign statements test
:tags: 10.6.1
*/
module top(clk, q, d, clr, set);

input clk, d, clr, set;
output q;
logic q;

always @(clr or set)
	if (clr)
		assign q = 0;
	else if (set)
		assign q = 1;
	else
		deassign q;

always @(posedge clk)
	q <= d;

endmodule
