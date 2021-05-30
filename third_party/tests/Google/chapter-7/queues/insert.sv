// Copyright (C) 2019-2021  The SymbiFlow Authors.
//
// Use of this source code is governed by a ISC-style
// license that can be found in the LICENSE file or at
// https://opensource.org/licenses/ISC
//
// SPDX-License-Identifier: ISC


/*
:name: insert
:description: Test queues insert function support
:tags: 7.10.2.2 7.10.2
:type: simulation parsing
*/
module top ();

int q[$];

initial begin
	q.insert(0, 1);
	$display(":assert: (%d == 1)", q.size);
	$display(":assert: (%d == 1)", q[0]);
end

endmodule
