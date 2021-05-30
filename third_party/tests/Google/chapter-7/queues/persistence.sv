// Copyright (C) 2019-2021  The SymbiFlow Authors.
//
// Use of this source code is governed by a ISC-style
// license that can be found in the LICENSE file or at
// https://opensource.org/licenses/ISC
//
// SPDX-License-Identifier: ISC


/*
:name: queues-elements-persistence
:description: Test status of persistence of references to elements of queue
:tags: 7.10.3
:type: simulation parsing
*/
module top ();

int q[$];

task automatic fun(ref int e);
	$display(":assert: (%d == 2)", e);
	#100
	e = 10;
	$display(":assert: (%d == 10)", e);
endtask

initial begin
	q.push_back(1);
	q.push_back(2);
	q.push_back(3);
	$display(":assert: ((%d == 1) and (%d == 2) and (%d == 3))",
		q[0], q[1], q[2]);
	fun(q[1]);
end

initial begin
	#50
	$display(":assert: (%d == 2)", q[1]);
	q.delete();
	#100;
	$display(":assert: (%d == 0)", q.size);
end

endmodule
