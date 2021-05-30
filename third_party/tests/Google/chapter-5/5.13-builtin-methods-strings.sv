// Copyright (C) 2019-2021  The SymbiFlow Authors.
//
// Use of this source code is governed by a ISC-style
// license that can be found in the LICENSE file or at
// https://opensource.org/licenses/ISC
//
// SPDX-License-Identifier: ISC


/*
:name: builtin-methods-string
:description: Check if built-in methods can be called
:tags: 5.13
*/
module top();
  string a = "test";

  initial begin;
    $display("length check: %d\n", a.len());
  end
endmodule
