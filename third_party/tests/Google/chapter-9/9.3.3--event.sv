// Copyright (C) 2019-2021  The SymbiFlow Authors.
//
// Use of this source code is governed by a ISC-style
// license that can be found in the LICENSE file or at
// https://opensource.org/licenses/ISC
//
// SPDX-License-Identifier: ISC


/*
:name: event_order
:description: event order test
:tags: 9.3.3
*/
module block_tb ();
	event ev;
	reg [3:0] a = 0;
	initial fork
		begin
			a = 'h3;
			#20;
			->ev;
		end
		begin
			@ev
			a = 'h4;
		end
	join
endmodule
