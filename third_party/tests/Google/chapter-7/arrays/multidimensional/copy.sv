// Copyright (C) 2019-2021  The SymbiFlow Authors.
//
// Use of this source code is governed by a ISC-style
// license that can be found in the LICENSE file or at
// https://opensource.org/licenses/ISC
//
// SPDX-License-Identifier: ISC


/*
:name: copy
:description: Test multidimensional word copy
:tags: 7.4.5
:type: simulation parsing
*/

module top ();

bit [3:0] [7:0] arr_a [1:10];
bit [3:0] [7:0] arr_b [1:10];

initial begin
	arr_a[1] = 32'hdeadbeef;
	$display(":assert: ('%h' == 'deadbeef')", arr_a[1]);

	arr_b[2] = arr_a[1];
	$display(":assert: ('%h' == 'deadbeef')", arr_b[2]);
end

endmodule
