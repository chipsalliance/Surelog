// Copyright (C) 2019-2021  The SymbiFlow Authors.
//
// Use of this source code is governed by a ISC-style
// license that can be found in the LICENSE file or at
// https://opensource.org/licenses/ISC
//
// SPDX-License-Identifier: ISC


/*
:name: property_test
:description: property test
:tags: 16.12
*/
module top();

logic clk;
logic a;

assert property ( @(posedge clk) (a == 1));

endmodule
