// Copyright (C) 2019-2021  The SymbiFlow Authors.
//
// Use of this source code is governed by a ISC-style
// license that can be found in the LICENSE file or at
// https://opensource.org/licenses/ISC
//
// SPDX-License-Identifier: ISC


/*
:name: void
:description: void type tests
:tags: 6.13
:type: simulation parsing
*/
module top();
	function void fun();
		$display(":assert:(True)");
	endfunction

	initial
		fun();
endmodule
