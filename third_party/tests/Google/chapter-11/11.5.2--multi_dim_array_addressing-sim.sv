// Copyright (C) 2019-2021  The SymbiFlow Authors.
//
// Use of this source code is governed by a ISC-style
// license that can be found in the LICENSE file or at
// https://opensource.org/licenses/ISC
//
// SPDX-License-Identifier: ISC


/*
:name: multi_dim_array_addressing_sim
:description: multi-dimensional array addressing simulation test
:type: simulation parsing
:tags: 11.5.2
*/
module top();
logic [7:0] mem [0:1023][0:3];
logic [7:0] a;

initial begin
    mem[123][2] = 125;
	a = mem[123][2];
    $display(":assert: (125 == %d)", a);
end

endmodule
