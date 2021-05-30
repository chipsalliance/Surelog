// Copyright (C) 2019-2021  The SymbiFlow Authors.
//
// Use of this source code is governed by a ISC-style
// license that can be found in the LICENSE file or at
// https://opensource.org/licenses/ISC
//
// SPDX-License-Identifier: ISC


/*
:name: enum_name
:description: enum name method tests
:tags: 6.19.5.6
*/
module top();
	typedef enum {a, b, c, d} e;

	initial begin
		e val = a;
		string s = val.name();
	end
endmodule
