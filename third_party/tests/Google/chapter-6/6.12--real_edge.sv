// Copyright (C) 2019-2021  The SymbiFlow Authors.
//
// Use of this source code is governed by a ISC-style
// license that can be found in the LICENSE file or at
// https://opensource.org/licenses/ISC
//
// SPDX-License-Identifier: ISC


/*
:name: real_edge
:description: real edge event tests
:should_fail_because: it is illegal to use edge event controls on real type
:tags: 6.12
:type: simulation
*/
module top();
	real a = 0.5;
	always @(posedge a)
		$display("posedge");
endmodule
