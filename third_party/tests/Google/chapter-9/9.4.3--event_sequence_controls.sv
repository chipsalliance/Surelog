// Copyright (C) 2019-2021  The SymbiFlow Authors.
//
// Use of this source code is governed by a ISC-style
// license that can be found in the LICENSE file or at
// https://opensource.org/licenses/ISC
//
// SPDX-License-Identifier: ISC


/*
:name: event_sequence_controls
:description: event sequence
:tags: 9.4.3
*/
module block_tb ();
	reg a = 0;
	wire b = 1;
	reg enable = 0;

	initial begin
		#10 enable = 1;
	end

	initial begin
		wait (enable) #10 a = b;
	end
endmodule
