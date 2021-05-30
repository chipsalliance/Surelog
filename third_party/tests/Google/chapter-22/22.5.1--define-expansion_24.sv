// Copyright (C) 2019-2021  The SymbiFlow Authors.
//
// Use of this source code is governed by a ISC-style
// license that can be found in the LICENSE file or at
// https://opensource.org/licenses/ISC
//
// SPDX-License-Identifier: ISC


/*
:name: 22.5.1--define_expansion_24
:description: Test
:tags: 22.5.1
:type: preprocessing
*/
module top ();
`define HI Hello
`define LO "`HI, world"
`define H(x) "Hello, x"
initial begin
	$display("`HI, world");
	$display(`LO);
	$display(`H(world));
end
endmodule
