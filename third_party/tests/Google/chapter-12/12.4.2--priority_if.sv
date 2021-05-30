// Copyright (C) 2019-2021  The SymbiFlow Authors.
//
// Use of this source code is governed by a ISC-style
// license that can be found in the LICENSE file or at
// https://opensource.org/licenses/ISC
//
// SPDX-License-Identifier: ISC


/*
:name: priority_if
:description: A module testing priority-if statement
:tags: 12.4.2
*/
module if_tb ();
	wire [3:0] a = 0;
	reg [1:0] b = 0;
	always @* begin
		priority if(a[0] == 0) b = 1;
		else if(a[1] == 0) b = 2;
	end
endmodule
