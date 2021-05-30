// Copyright (C) 2019-2021  The SymbiFlow Authors.
//
// Use of this source code is governed by a ISC-style
// license that can be found in the LICENSE file or at
// https://opensource.org/licenses/ISC
//
// SPDX-License-Identifier: ISC


/*
:name: function_automatic
:description: automatic function test
:tags: 13.4.2
:type: simulation parsing
*/
module top();

function automatic int add(int val);
	int a = 0;
	a = a + val;
	return a;
endfunction

initial
	begin
		$display(":assert: (%d == 5)", add(5));
		$display(":assert: (%d == 5)", add(5));
		$display(":assert: (%d == 5)", add(5));
		$display(":assert: (%d == 5)", add(5));
	end

endmodule
