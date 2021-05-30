// Copyright (C) 2019-2021  The SymbiFlow Authors.
//
// Use of this source code is governed by a ISC-style
// license that can be found in the LICENSE file or at
// https://opensource.org/licenses/ISC
//
// SPDX-License-Identifier: ISC


/*
:name: variable_multiple_assignments
:description: Variable multiple assignments tests
:should_fail_because: it shall be an error to have multiple continuous assignments
:tags: 6.5
:type: simulation
*/
module top();
	int v;

	assign v = 12;
	assign v = 13;
endmodule
