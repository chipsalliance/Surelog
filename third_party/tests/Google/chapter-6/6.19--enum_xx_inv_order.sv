// Copyright (C) 2019-2021  The SymbiFlow Authors.
//
// Use of this source code is governed by a ISC-style
// license that can be found in the LICENSE file or at
// https://opensource.org/licenses/ISC
//
// SPDX-License-Identifier: ISC


/*
:name: enum_xx_inv_order
:description: unassigned name following enum with x tests
:should_fail_because: An unassigned enumerated name that follows an enum name with x or z assignments shall be a syntax error.
:tags: 6.19
:type: simulation
*/
module top();
	enum integer {a=0, b={32{1'bx}}, c} val;
endmodule
