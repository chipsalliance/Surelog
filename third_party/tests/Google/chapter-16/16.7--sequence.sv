// Copyright (C) 2019-2021  The SymbiFlow Authors.
//
// Use of this source code is governed by a ISC-style
// license that can be found in the LICENSE file or at
// https://opensource.org/licenses/ISC
//
// SPDX-License-Identifier: ISC


/*
:name: sequence_test
:description: sequence test
:tags: 16.7
*/

module top();

logic clk;
logic a;
logic b;

sequence seq;
    @(posedge clk) a ##1 b;
endsequence

assert property (seq);

endmodule
