// Copyright (C) 2019-2021  The SymbiFlow Authors.
//
// Use of this source code is governed by a ISC-style
// license that can be found in the LICENSE file or at
// https://opensource.org/licenses/ISC
//
// SPDX-License-Identifier: ISC


/*
:name: if
:description: A module testing if statement
:tags: 12.4
*/
module if_tb ();
	wire a = 0;
	reg b = 0;
	always @* begin
		if(a) b = 1;
	end
endmodule
