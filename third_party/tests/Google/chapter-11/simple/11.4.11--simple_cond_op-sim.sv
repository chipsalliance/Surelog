// Copyright (C) 2019-2021  The SymbiFlow Authors.
//
// Use of this source code is governed by a ISC-style
// license that can be found in the LICENSE file or at
// https://opensource.org/licenses/ISC
//
// SPDX-License-Identifier: ISC


/*
:name: simple_cond_op_sim
:description: minimal ?: operator simulation test (without result verification)
:type: simulation parsing
:tags: 11.4.11
*/
module top(input a, output b);

assign b = (a) ? 0 : 1;

endmodule
