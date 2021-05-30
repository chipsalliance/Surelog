// Copyright (C) 2019-2021  The SymbiFlow Authors.
//
// Use of this source code is governed by a ISC-style
// license that can be found in the LICENSE file or at
// https://opensource.org/licenses/ISC
//
// SPDX-License-Identifier: ISC


/*
:name: stream_concat
:description: stream concatenation test
:tags: 11.4.14.1
*/
module top();

int a = {"A", "B", "C", "D"};
int b = {"E", "F", "G", "H"};
logic [63:0] c;

initial begin
	c = {>> 8 {a, b}};
end

endmodule
