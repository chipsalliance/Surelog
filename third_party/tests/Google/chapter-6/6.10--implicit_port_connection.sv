// Copyright (C) 2019-2021  The SymbiFlow Authors.
//
// Use of this source code is governed by a ISC-style
// license that can be found in the LICENSE file or at
// https://opensource.org/licenses/ISC
//
// SPDX-License-Identifier: ISC


/*
:name: implicit_port_connection
:description: implicit port connection tests
:tags: 6.10
*/
module top();
	wire a = 1;
	wire b = 0;
	wire d;

	test mod(a, b, c);

	assign d = c;
endmodule

module test(input a, input b, output c);
	assign c = a | b;
endmodule
