// Copyright (C) 2019-2021  The SymbiFlow Authors.
//
// Use of this source code is governed by a ISC-style
// license that can be found in the LICENSE file or at
// https://opensource.org/licenses/ISC
//
// SPDX-License-Identifier: ISC


/*
:name: force_release
:description: force-release statements test
:tags: 10.6.2
*/
module top(clk, q, d, f1, f0);

input clk, d, f1, f0;
output q;
logic q;

always @(f1 or f0)
	if (f0)
		force q = 0;
	else if (f1)
		force q = 1;
	else
		release q;

always @(posedge clk)
	q <= d;

endmodule
