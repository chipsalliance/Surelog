// Copyright (C) 2019-2021  The SymbiFlow Authors.
//
// Use of this source code is governed by a ISC-style
// license that can be found in the LICENSE file or at
// https://opensource.org/licenses/ISC
//
// SPDX-License-Identifier: ISC


/*
:name: operations-on-arrays-treat-as-integer
:description: Test packed arrays operations support (treat array as integer)
:tags: 7.4.3
:type: simulation parsing
*/
module top ();

bit [7:0] arr_a;
bit [7:0] arr_b;

initial begin
	arr_a = 8'd17;
	arr_b = (arr_a + 29);
	$display(":assert: (%d == 46)", arr_b);
end

endmodule
