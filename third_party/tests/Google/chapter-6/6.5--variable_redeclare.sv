// Copyright (C) 2019-2021  The SymbiFlow Authors.
//
// Use of this source code is governed by a ISC-style
// license that can be found in the LICENSE file or at
// https://opensource.org/licenses/ISC
//
// SPDX-License-Identifier: ISC


/*
:name: variable_redeclare
:description: Variable redeclaration tests
:should_fail_because: Variable redeclaration
:tags: 6.5
:type: simulation
*/
module top();
	reg v;
	wire v;
endmodule
