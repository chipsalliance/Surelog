// Copyright (C) 2019-2021  The SymbiFlow Authors.
//
// Use of this source code is governed by a ISC-style
// license that can be found in the LICENSE file or at
// https://opensource.org/licenses/ISC
//
// SPDX-License-Identifier: ISC


/*
:name: push_front_assign
:description: Update queue by assignment (push_front)
:tags: 7.10.4
:type: simulation parsing
*/
module top ();

int q[$];

initial begin
	q = { 2, q };
	q = { 3, q };
	q = { 4, q };
	$display(":assert: (%d == 3)", q.size);
	$display(":assert: (%d == 4)", q[0]);
end

endmodule
