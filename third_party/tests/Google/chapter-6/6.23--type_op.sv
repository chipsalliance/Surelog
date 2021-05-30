// Copyright (C) 2019-2021  The SymbiFlow Authors.
//
// Use of this source code is governed by a ISC-style
// license that can be found in the LICENSE file or at
// https://opensource.org/licenses/ISC
//
// SPDX-License-Identifier: ISC


/*
:name: type_op
:description: type operator tests
:tags: 6.23
*/
module top();
	real a = 4.76;
	real b = 0.74;
	var type(a+b) c;
endmodule
