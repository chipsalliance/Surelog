// Copyright (C) 2019-2021  The SymbiFlow Authors.
//
// Use of this source code is governed by a ISC-style
// license that can be found in the LICENSE file or at
// https://opensource.org/licenses/ISC
//
// SPDX-License-Identifier: ISC


/*
:name: function
:description: function test
:tags: 13.4
:type: simulation parsing
*/
module top();

function int test(int val);
	return val + 1;
endfunction

initial
	$display(":assert: (%d == 2)", test(1));

endmodule
