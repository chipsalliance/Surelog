// Copyright (C) 2019-2021  The SymbiFlow Authors.
//
// Use of this source code is governed by a ISC-style
// license that can be found in the LICENSE file or at
// https://opensource.org/licenses/ISC
//
// SPDX-License-Identifier: ISC


/*
:name: enum_xx
:description: enum with x tests
:tags: 6.19
*/
module top();
	enum integer {a=0, b={32{1'bx}}, c=1} val;
endmodule
