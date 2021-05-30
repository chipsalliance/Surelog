// Copyright (C) 2019-2021  The SymbiFlow Authors.
//
// Use of this source code is governed by a ISC-style
// license that can be found in the LICENSE file or at
// https://opensource.org/licenses/ISC
//
// SPDX-License-Identifier: ISC


/*
:name: jump_return_expr
:description: A module testing return <expr> statement
:tags: 12.8
*/
module jump_tb ();
	function int fun(input int a);
		return a * 3;
	endfunction
	initial begin
		for (int i = 0; i < 256; i++)begin
			$display(fun(i));
		end
	end
endmodule
