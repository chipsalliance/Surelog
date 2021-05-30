// Copyright (C) 2019-2021  The SymbiFlow Authors.
//
// Use of this source code is governed by a ISC-style
// license that can be found in the LICENSE file or at
// https://opensource.org/licenses/ISC
//
// SPDX-License-Identifier: ISC


/*
:name: parameter_dep
:description: parameter depending on another parameter tests
:tags: 6.20.2
*/
module top();
	parameter p1 = 123;
	parameter p2 = p1 * 3;
endmodule
