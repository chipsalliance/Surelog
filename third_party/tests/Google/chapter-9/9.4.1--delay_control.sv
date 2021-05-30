// Copyright (C) 2019-2021  The SymbiFlow Authors.
//
// Use of this source code is governed by a ISC-style
// license that can be found in the LICENSE file or at
// https://opensource.org/licenses/ISC
//
// SPDX-License-Identifier: ISC


/*
:name: delay_control
:description: delay control
:tags: 9.4.1
*/
module block_tb ();
	reg [3:0] a = 0;
	initial begin
		#10 a = 'h1;
		#10 a = 'h2;
		#10 a = 'h3;
		#10 a = 'h4;
	end
endmodule
