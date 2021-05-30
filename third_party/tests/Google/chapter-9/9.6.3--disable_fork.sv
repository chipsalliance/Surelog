// Copyright (C) 2019-2021  The SymbiFlow Authors.
//
// Use of this source code is governed by a ISC-style
// license that can be found in the LICENSE file or at
// https://opensource.org/licenses/ISC
//
// SPDX-License-Identifier: ISC


/*
:name: disable_fork
:description: disable fork
:tags: 9.6.3
*/
module fork_tb ();
	reg a = 0;
	reg b = 0;
	reg c = 0;
	initial begin
		fork
			#50 a = 1;
			#100 b = 1;
			#150 c = 1;
		join_any
		disable fork;
	end
endmodule
