// Copyright (C) 2019-2021  The SymbiFlow Authors.
//
// Use of this source code is governed by a ISC-style
// license that can be found in the LICENSE file or at
// https://opensource.org/licenses/ISC
//
// SPDX-License-Identifier: ISC


/*
:name: blocking_assignment
:description: blocking assignment test
:tags: 10.4.1
:type: simulation parsing
*/
module top();

logic a = 3;
logic b = 2;

initial begin
	a = 1;
	b = a;
	$display(":assert: (%d == %d)", a, b);
end

endmodule
