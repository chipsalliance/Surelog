// Copyright (C) 2019-2021  The SymbiFlow Authors.
//
// Use of this source code is governed by a ISC-style
// license that can be found in the LICENSE file or at
// https://opensource.org/licenses/ISC
//
// SPDX-License-Identifier: ISC


/*
:name: function_void_return
:description: void function return value test
:should_fail_because: void function returns value
:tags: 13.4.1
:type: simulation
*/
module top();

function void add(int a, int b);
	$display("%d+%d=", a, b);
	return a + b;
endfunction

initial
	$display("%d", add(45, 90));

endmodule
