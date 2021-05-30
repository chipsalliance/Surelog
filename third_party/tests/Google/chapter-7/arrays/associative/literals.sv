// Copyright (C) 2019-2021  The SymbiFlow Authors.
//
// Use of this source code is governed by a ISC-style
// license that can be found in the LICENSE file or at
// https://opensource.org/licenses/ISC
//
// SPDX-License-Identifier: ISC


/*
:name: associative-arrays-literals
:description: Test associative arrays literals support
:tags: 7.9.11 7.8
:type: simulation parsing
*/
module top ();

string words [int] = '{default: "hello"};

initial begin
	$display(":assert: ('%s' == 'hello')", words[1]);
	words[1] = "world";
	$display(":assert: (('%s' == 'hello') and ('%s' == 'world'))",
		words[0], words[1]);
end

endmodule
