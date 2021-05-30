// Copyright (C) 2019-2021  The SymbiFlow Authors.
//
// Use of this source code is governed by a ISC-style
// license that can be found in the LICENSE file or at
// https://opensource.org/licenses/ISC
//
// SPDX-License-Identifier: ISC


/*
:name: parallel_block_join_none
:description: parallel block check
:tags: 9.3.2
*/
module parallel_tb ();
	reg a = 0;
	reg b = 0;
	reg c = 0;
	initial
		fork
			a = 1;
			b = 0;
			c = 1;
		join_none
endmodule
