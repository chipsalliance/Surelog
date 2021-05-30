// Copyright (C) 2019-2021  The SymbiFlow Authors.
//
// Use of this source code is governed by a ISC-style
// license that can be found in the LICENSE file or at
// https://opensource.org/licenses/ISC
//
// SPDX-License-Identifier: ISC


/*
:name: simple_non_idx_part_select_sim
:description: minimal non-indexed part-select bit simulation test (without result verification)
:type: simulation parsing
:tags: 11.5.1
*/
module top(input [7:0] a, output [1:0] b);

assign b = a[7:6];

endmodule
