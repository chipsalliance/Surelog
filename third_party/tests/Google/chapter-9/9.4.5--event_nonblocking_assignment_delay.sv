// Copyright (C) 2019-2021  The SymbiFlow Authors.
//
// Use of this source code is governed by a ISC-style
// license that can be found in the LICENSE file or at
// https://opensource.org/licenses/ISC
//
// SPDX-License-Identifier: ISC


/*
:name: event_nonblocking_assignment_delay
:description: event non blk assignment delay
:tags: 9.4.5
*/
module block_tb ();
	reg a = 0;
	reg b = 1;

	initial begin
		a <= #10 b;
	end
endmodule
