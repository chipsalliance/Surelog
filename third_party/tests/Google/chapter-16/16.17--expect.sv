// Copyright (C) 2019-2021  The SymbiFlow Authors.
//
// Use of this source code is governed by a ISC-style
// license that can be found in the LICENSE file or at
// https://opensource.org/licenses/ISC
//
// SPDX-License-Identifier: ISC


/*
:name: expect_test
:description: expect test
:tags: 16.17
*/

module top();

logic clk;
logic a;
logic b;

initial begin
    expect (@(posedge clk) a ##1 b);
end

endmodule
