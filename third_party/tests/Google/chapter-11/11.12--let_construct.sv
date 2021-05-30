// Copyright (C) 2019-2021  The SymbiFlow Authors.
//
// Use of this source code is governed by a ISC-style
// license that can be found in the LICENSE file or at
// https://opensource.org/licenses/ISC
//
// SPDX-License-Identifier: ISC


/*
:name: let_construct
:description: let construct test
:tags: 11.12
*/
module top();

logic [3:0] a = 12;
logic [3:0] b = 15;
logic [3:0] c = 7;
logic d;

let op(x, y, z) = |((x | y) & z);

initial begin
	d = op(.x(a), .y(b), .z(c));
end

endmodule
