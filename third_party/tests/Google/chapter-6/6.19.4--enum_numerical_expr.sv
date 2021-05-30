// Copyright (C) 2019-2021  The SymbiFlow Authors.
//
// Use of this source code is governed by a ISC-style
// license that can be found in the LICENSE file or at
// https://opensource.org/licenses/ISC
//
// SPDX-License-Identifier: ISC


/*
:name: enum_numerical_expr
:description: enum numerical expression tests
:tags: 6.19.4
*/
module top();
	typedef enum {a, b, c, d} e;

	initial begin
		integer i;
		e val;
		val = a;
		i = val * 4;
	end
endmodule
