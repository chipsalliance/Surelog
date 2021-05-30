// Copyright (C) 2019-2021  The SymbiFlow Authors.
//
// Use of this source code is governed by a ISC-style
// license that can be found in the LICENSE file or at
// https://opensource.org/licenses/ISC
//
// SPDX-License-Identifier: ISC


/*
:name: ordering-methods-shuffle
:description: Test support of shuffle method on unpacked arrays
:tags: 7.12.2 7.4.2
:type: simulation parsing
*/
module top ();

int ia[] = { 1, 2, 3, 4, 5 };

initial begin
	$display(":info: { %d, %d, %d, %d, %d }",
		ia[0], ia[1], ia[2], ia[3], ia[4]);
	ia.shuffle;
	$display(":info: { %d, %d, %d, %d, %d }",
		ia[0], ia[1], ia[2], ia[3], ia[4]);
end

endmodule
