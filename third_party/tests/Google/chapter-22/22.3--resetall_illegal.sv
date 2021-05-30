// Copyright (C) 2019-2021  The SymbiFlow Authors.
//
// Use of this source code is governed by a ISC-style
// license that can be found in the LICENSE file or at
// https://opensource.org/licenses/ISC
//
// SPDX-License-Identifier: ISC


/*
:name: 22.3--resetall_illegal
:description: It shall be illegal for the `resetall directive to be specified within a design element.
:should_fail_because: It shall be illegal for the `resetall directive to be specified within a design element.
:tags: 22.3
:type: preprocessing parsing
*/
`resetall
module top ();
`resetall
endmodule
