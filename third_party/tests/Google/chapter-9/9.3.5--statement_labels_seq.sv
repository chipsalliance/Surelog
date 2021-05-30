// Copyright (C) 2019-2021  The SymbiFlow Authors.
//
// Use of this source code is governed by a ISC-style
// license that can be found in the LICENSE file or at
// https://opensource.org/licenses/ISC
//
// SPDX-License-Identifier: ISC


/*
:name: statement_labels_seq
:description: sequential block labels check
:tags: 9.3.5
*/
module block_tb ();
	reg a = 0;
	reg b = 0;
	reg c = 0;
	initial
		name: begin
			a = 1;
			b = a;
			c = b;
		end: name
endmodule
