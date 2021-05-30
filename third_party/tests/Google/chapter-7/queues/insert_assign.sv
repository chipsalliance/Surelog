// Copyright (C) 2019-2021  The SymbiFlow Authors.
//
// Use of this source code is governed by a ISC-style
// license that can be found in the LICENSE file or at
// https://opensource.org/licenses/ISC
//
// SPDX-License-Identifier: ISC


/*
:name: insert-assign
:description: Update queue by assignment (insert)
:tags: 7.10.4
:type: simulation parsing
*/
module top ();

int q[$];

initial begin
	q = { 1, 2, 3, 4 };
	q = { q[0:1], 10, q[2:$] }; // q.insert(2, 10)
	$display(":assert: (%d == 5)", q.size);
	$display(":assert: (%d == 10)", q[2]);
end

endmodule
