// Copyright (C) 2019-2021  The SymbiFlow Authors.
//
// Use of this source code is governed by a ISC-style
// license that can be found in the LICENSE file or at
// https://opensource.org/licenses/ISC
//
// SPDX-License-Identifier: ISC


/*
:name: tagged_union_member_access_sim
:description: tagged union member access simulation test
:type: simulation parsing
:tags: 11.9
*/
module top();

typedef union tagged {
	void Invalid;
	int Valid;
} u_int;

u_int a;

int b;

initial begin
	a = tagged Valid(42);
	b = a.Valid;
    $display(":assert: (42 == %d)", b);
end

endmodule
