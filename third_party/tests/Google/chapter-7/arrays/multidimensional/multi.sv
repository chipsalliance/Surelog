// Copyright (C) 2019-2021  The SymbiFlow Authors.
//
// Use of this source code is governed by a ISC-style
// license that can be found in the LICENSE file or at
// https://opensource.org/licenses/ISC
//
// SPDX-License-Identifier: ISC


/*
:name: multi-declaration
:description: Test multidimensional arrays
:tags: 7.4.5
*/

module top ();

// Same packed dimensions
bit [7:0] [31:0] arr_a [1:5] [1:10], arr_b [0:255];

endmodule
