// Copyright (C) 2019-2021  The SymbiFlow Authors.
//
// Use of this source code is governed by a ISC-style
// license that can be found in the LICENSE file or at
// https://opensource.org/licenses/ISC
//
// SPDX-License-Identifier: ISC


/*
:name: if_pattern
:description: A module testing pattern matching in if statements
:tags: 12.6.2
*/
module case_tb ();

	typedef union tagged {
		struct {
			bit [3:0] val1, val2;
		} a;
		struct {
			bit [7:0] val1, val2;
		} b;
		struct {
			bit [15:0] val1, val2;
		} c;
	} u;

	u tmp;

	initial if (tmp matches tagged a '{4'b01zx, .v})
		$display("a %d", v);
		
		
endmodule
