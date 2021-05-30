// Copyright (C) 2019-2021  The SymbiFlow Authors.
//
// Use of this source code is governed by a ISC-style
// license that can be found in the LICENSE file or at
// https://opensource.org/licenses/ISC
//
// SPDX-License-Identifier: ISC


/*
:name: repeat_loop
:description: A module testing repeat loop
:tags: 12.7.2
*/
module repeat_tb ();
	int a = 128;
	initial begin
		repeat(a)
			$display("repeat");
	end
endmodule
