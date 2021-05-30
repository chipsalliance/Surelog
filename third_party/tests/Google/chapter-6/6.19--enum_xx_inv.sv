// Copyright (C) 2019-2021  The SymbiFlow Authors.
//
// Use of this source code is governed by a ISC-style
// license that can be found in the LICENSE file or at
// https://opensource.org/licenses/ISC
//
// SPDX-License-Identifier: ISC


/*
:name: enum_xx_inv
:description: invalid enum with x tests
:should_fail_because: An enumerated name with x or z assignments assigned to an enum with no explicit data type or an explicit2-state declaration shall be a syntax error
:tags: 6.19
:type: simulation
*/
module top();
	enum bit [1:0] {a=0, b=2'bxx, c=1} val;
endmodule
