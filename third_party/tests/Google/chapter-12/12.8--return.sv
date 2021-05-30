// Copyright (C) 2019-2021  The SymbiFlow Authors.
//
// Use of this source code is governed by a ISC-style
// license that can be found in the LICENSE file or at
// https://opensource.org/licenses/ISC
//
// SPDX-License-Identifier: ISC


/*
:name: jump_return
:description: A module testing return statement
:tags: 12.8
*/
module jump_tb ();
	function void fun(input int a);
		$display("a");
		if(a == 21)
			return;
		$display(a);
		return;
	endfunction
	initial begin
		for (int i = 0; i < 256; i++)begin
			fun(i);
		end
	end
endmodule
