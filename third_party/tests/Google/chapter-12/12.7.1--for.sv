// Copyright (C) 2019-2021  The SymbiFlow Authors.
//
// Use of this source code is governed by a ISC-style
// license that can be found in the LICENSE file or at
// https://opensource.org/licenses/ISC
//
// SPDX-License-Identifier: ISC


/*
:name: for_loop
:description: A module testing for loop
:tags: 12.7.1
*/
module for_tb ();
	initial begin
		for (int i = 0; i < 256; i++)
			$display("%d", i);
	end
endmodule
