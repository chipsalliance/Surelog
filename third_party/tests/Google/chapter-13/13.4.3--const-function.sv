// Copyright (C) 2019-2021  The SymbiFlow Authors.
//
// Use of this source code is governed by a ISC-style
// license that can be found in the LICENSE file or at
// https://opensource.org/licenses/ISC
//
// SPDX-License-Identifier: ISC


/*
:name: const_function
:description: const function test
:tags: 13.4.3
:type: simulation parsing
*/
module top();

localparam a = fun(3);

function int fun(int val);
	return val + 1;
endfunction

initial
	$display(":assert: (%d == 4)", a);

endmodule
