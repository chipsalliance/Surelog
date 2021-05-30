// Copyright (C) 2019-2021  The SymbiFlow Authors.
//
// Use of this source code is governed by a ISC-style
// license that can be found in the LICENSE file or at
// https://opensource.org/licenses/ISC
//
// SPDX-License-Identifier: ISC


/*
:name: event_comma_op
:description: event comma operator
:tags: 9.4.2.1
*/
module block_tb ();
	wire a = 0;
	wire b = 0;
	wire c = 0;
	wire d = 0;
	reg out;
	always @(a, b, c, d)
		out = (a | b) & (c | d);
endmodule
