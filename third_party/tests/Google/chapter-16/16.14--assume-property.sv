// Copyright (C) 2019-2021  The SymbiFlow Authors.
//
// Use of this source code is governed by a ISC-style
// license that can be found in the LICENSE file or at
// https://opensource.org/licenses/ISC
//
// SPDX-License-Identifier: ISC


/*
:name: assume_property_test
:description: assume property test
:tags: 16.14
*/
module top();

logic clk;
logic a;

assume property ( @(posedge clk) (a == 1));

endmodule
