// Copyright (C) 2019-2021  The SymbiFlow Authors.
//
// Use of this source code is governed by a ISC-style
// license that can be found in the LICENSE file or at
// https://opensource.org/licenses/ISC
//
// SPDX-License-Identifier: ISC


/*
:name: enum_prev
:description: enum prev method tests
:tags: 6.19.5.4
*/
module top();
	typedef enum {a, b, c, d} e;

	initial begin
		e val = b;
		val = val.prev();
	end
endmodule
