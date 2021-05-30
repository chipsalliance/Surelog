// Copyright (C) 2019-2021  The SymbiFlow Authors.
//
// Use of this source code is governed by a ISC-style
// license that can be found in the LICENSE file or at
// https://opensource.org/licenses/ISC
//
// SPDX-License-Identifier: ISC


/*
:name: event_conditional
:description: event conditional
:tags: 9.4.2.3
*/
module block_tb ();
	wire clk = 0;
	wire en = 0;
	wire a = 0;
	reg y;
	always @(posedge clk iff en == 1)
		y <= a;
endmodule
