// Copyright (C) 2019-2021  The SymbiFlow Authors.
//
// Use of this source code is governed by a ISC-style
// license that can be found in the LICENSE file or at
// https://opensource.org/licenses/ISC
//
// SPDX-License-Identifier: ISC


/*
:name: always_latch_expr
:description: always_latch check
:tags: 9.2.2.3
*/
module always_tb ();
	wire a = 0;
	wire b = 0;
	reg q = 0;
	always_latch
		if(a) q <= b;
endmodule
