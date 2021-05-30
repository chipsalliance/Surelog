// Copyright (C) 2019-2021  The SymbiFlow Authors.
//
// Use of this source code is governed by a ISC-style
// license that can be found in the LICENSE file or at
// https://opensource.org/licenses/ISC
//
// SPDX-License-Identifier: ISC


/*
:name: simple_set_member_sim
:description: minimal inside operator simulation test (without result verification)
:type: simulation parsing
:tags: 11.4.13
*/
module top(input [3:0] a, output b);

assign b = (a inside {2, 3, 4, 5});

endmodule
