// Copyright (C) 2019-2021  The SymbiFlow Authors.
//
// Use of this source code is governed by a ISC-style
// license that can be found in the LICENSE file or at
// https://opensource.org/licenses/ISC
//
// SPDX-License-Identifier: ISC


/*
:name: event_control_posedge
:description: event control
:tags: 9.4.2
*/
module block_tb ();
	reg [3:0] a = 0;
	wire clk = 0;
	always @(posedge clk) a = ~a;
endmodule
