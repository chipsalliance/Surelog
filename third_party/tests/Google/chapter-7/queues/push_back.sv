// Copyright (C) 2019-2021  The SymbiFlow Authors.
//
// Use of this source code is governed by a ISC-style
// license that can be found in the LICENSE file or at
// https://opensource.org/licenses/ISC
//
// SPDX-License-Identifier: ISC


/*
:name: push_back
:description: Test queues push_back function support
:tags: 7.10.2.7 7.10.2
:type: simulation parsing
*/
module top ();

int q[$];

initial begin
	q.push_back(4);
	q.push_back(3);
	q.push_back(2);
	$display(":assert: (%d == 3)", q.size);
	$display(":assert: (%d == 4)", q[0]);
end

endmodule
