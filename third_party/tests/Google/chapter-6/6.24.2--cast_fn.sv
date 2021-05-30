// Copyright (C) 2019-2021  The SymbiFlow Authors.
//
// Use of this source code is governed by a ISC-style
// license that can be found in the LICENSE file or at
// https://opensource.org/licenses/ISC
//
// SPDX-License-Identifier: ISC


/*
:name: cast_fn
:description: $cast function
:tags: 6.24.2
*/
module top();
	int a;
	initial
		if (! $cast(a, 2.1 * 3.7))
			$display("cast failed");
endmodule
