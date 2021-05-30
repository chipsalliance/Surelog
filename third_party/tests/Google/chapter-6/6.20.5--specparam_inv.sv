// Copyright (C) 2019-2021  The SymbiFlow Authors.
//
// Use of this source code is governed by a ISC-style
// license that can be found in the LICENSE file or at
// https://opensource.org/licenses/ISC
//
// SPDX-License-Identifier: ISC


/*
:name: specparam_inv
:description: specparam assignment to param should be invalid
:should_fail_because: specparam assignment to param should be invalid
:tags: 6.20.5
:type: simulation
*/
module top();
	specparam delay = 50;
	parameter p = delay + 2;
endmodule
