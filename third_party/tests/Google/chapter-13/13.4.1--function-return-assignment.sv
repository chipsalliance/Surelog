// Copyright (C) 2019-2021  The SymbiFlow Authors.
//
// Use of this source code is governed by a ISC-style
// license that can be found in the LICENSE file or at
// https://opensource.org/licenses/ISC
//
// SPDX-License-Identifier: ISC


/*
:name: function_return_assignment
:description: function return value assignment test
:tags: 13.4.1
:type: simulation parsing
*/
module top();

function int add(int a, int b);
	add = a + b;
endfunction

initial
	$display(":assert: (%d == 90)", add(30, 60));

endmodule
