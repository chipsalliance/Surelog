// Copyright (C) 2019-2021  The SymbiFlow Authors.
//
// Use of this source code is governed by a ISC-style
// license that can be found in the LICENSE file or at
// https://opensource.org/licenses/ISC
//
// SPDX-License-Identifier: ISC


/*
:name: string_concat
:description: string concatenation test
:type: simulation parsing
:tags: 11.10.1
*/
module top();

bit [8*14:1] a;
bit [8*14:1] b;

initial begin
	a = "Test";
	b = "TEST";
	$display(":assert: ('TEST' in '%s')", {a, b});
	$display(":assert: ('Test' in '%s')", {a, b});
end

endmodule
