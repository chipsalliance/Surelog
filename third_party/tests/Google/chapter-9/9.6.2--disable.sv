// Copyright (C) 2019-2021  The SymbiFlow Authors.
//
// Use of this source code is governed by a ISC-style
// license that can be found in the LICENSE file or at
// https://opensource.org/licenses/ISC
//
// SPDX-License-Identifier: ISC


/*
:name: disable
:description: disable block
:tags: 9.6.2
*/
module fork_tb ();
	reg a = 0;
	reg b = 0;
	initial begin: block
		a = 1;
		disable block;
		b = 1;
	end
endmodule
