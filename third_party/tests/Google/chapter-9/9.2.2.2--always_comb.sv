// Copyright (C) 2019-2021  The SymbiFlow Authors.
//
// Use of this source code is governed by a ISC-style
// license that can be found in the LICENSE file or at
// https://opensource.org/licenses/ISC
//
// SPDX-License-Identifier: ISC


/*
:name: always_comb
:description: always_comb check
:tags: 9.2.2.2
*/
module always_tb ();
	wire a = 0;
	reg b = 0;
	always_comb
		b = ~a;
endmodule
