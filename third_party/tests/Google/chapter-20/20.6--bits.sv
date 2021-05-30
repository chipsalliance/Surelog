// Copyright (C) 2019-2021  The SymbiFlow Authors.
//
// Use of this source code is governed by a ISC-style
// license that can be found in the LICENSE file or at
// https://opensource.org/licenses/ISC
//
// SPDX-License-Identifier: ISC


/*
:name: bits_function
:description: $bits test
:tags: 20.6
:type: simulation parsing
*/

module top();

initial begin
	logic [31:0] val;
	$display(":assert: (%d == 32)", $bits(val));
end

endmodule
