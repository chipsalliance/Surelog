// Copyright (C) 2019-2021  The SymbiFlow Authors.
//
// Use of this source code is governed by a ISC-style
// license that can be found in the LICENSE file or at
// https://opensource.org/licenses/ISC
//
// SPDX-License-Identifier: ISC


/*
:name: clocking_block_signals
:description: clocking block with signals test
:should_fail_because: assigning to net from procedural context
:type: simulation
:tags: 14.3
*/
module top(input clk, input a, output b, output c);

clocking ck1 @(posedge clk);
	default input #10ns output #5ns;
	input a;
	output b;
	output #3ns c;
endclocking

always_ff @(posedge clk) begin
	b <= a;
	c <= a;
end

endmodule
