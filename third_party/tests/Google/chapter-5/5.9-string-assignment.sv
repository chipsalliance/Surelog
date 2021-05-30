// Copyright (C) 2019-2021  The SymbiFlow Authors.
//
// Use of this source code is governed by a ISC-style
// license that can be found in the LICENSE file or at
// https://opensource.org/licenses/ISC
//
// SPDX-License-Identifier: ISC


/*
:name: string-assignment
:description: String assignment tests
:tags: 5.9
*/
module top();
  byte        a;
  bit   [7:0] b;
  logic [7:0] c;

  initial begin;
    a = "a";
    b = "b";
    c = "c";
  end

endmodule
