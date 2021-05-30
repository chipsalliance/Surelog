// Copyright (C) 2019-2021  The SymbiFlow Authors.
//
// Use of this source code is governed by a ISC-style
// license that can be found in the LICENSE file or at
// https://opensource.org/licenses/ISC
//
// SPDX-License-Identifier: ISC


/*
:name: real_bit_select
:description: real bit select tests
:should_fail_because: it is illegal to do bit select on real data type
:tags: 6.12
:type: simulation
*/
module top();
	real a = 0.5;
	wire [3:0] b;
	wire c;

	assign c = b[a];
endmodule
