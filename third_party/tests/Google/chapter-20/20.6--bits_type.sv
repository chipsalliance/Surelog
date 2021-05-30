// Copyright (C) 2019-2021  The SymbiFlow Authors.
//
// Use of this source code is governed by a ISC-style
// license that can be found in the LICENSE file or at
// https://opensource.org/licenses/ISC
//
// SPDX-License-Identifier: ISC


/*
:name: bits_type_function
:description: $bits with type argument
:tags: 20.6
:type: simulation parsing
*/

module top();

typedef struct packed {
	logic val1;
	bit [7:0] val2;
} mystruct;

initial begin
	$display(":assert: (%d == 9)", $bits(mystruct));
end

endmodule
