// Copyright (C) 2019-2021  The SymbiFlow Authors.
//
// Use of this source code is governed by a ISC-style
// license that can be found in the LICENSE file or at
// https://opensource.org/licenses/ISC
//
// SPDX-License-Identifier: ISC


/*
:name: enum_last
:description: enum last method tests
:tags: 6.19.5.2
*/
module top();
	typedef enum {a, b, c, d} e;

	initial begin
		e val = a;
		val = val.last();
	end
endmodule
