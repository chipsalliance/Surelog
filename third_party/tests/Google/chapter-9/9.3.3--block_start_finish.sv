// Copyright (C) 2019-2021  The SymbiFlow Authors.
//
// Use of this source code is governed by a ISC-style
// license that can be found in the LICENSE file or at
// https://opensource.org/licenses/ISC
//
// SPDX-License-Identifier: ISC


/*
:name: block_start_finish
:description: block start finish check
:tags: 9.3.3
*/
module block_tb ();
	reg [3:0] a = 0;
	initial begin
		fork
			#200 a = 'h1;
			#150 a = 'h2;
			#100 a = 'h3;
			#50  a = 'h4;
		join

		fork
			#200 a = 'h5;
			#150 a = 'h6;
			#100 a = 'h7;
			#50  a = 'h8;
		join
	end
endmodule
