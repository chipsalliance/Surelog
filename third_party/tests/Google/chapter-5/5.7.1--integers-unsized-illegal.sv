// Copyright (C) 2019-2021  The SymbiFlow Authors.
//
// Use of this source code is governed by a ISC-style
// license that can be found in the LICENSE file or at
// https://opensource.org/licenses/ISC
//
// SPDX-License-Identifier: ISC


/*
:name: integers-unsized-illegal
:description: Integer literal constants
:should_fail_because: hexadecimal format requires 'h
:tags: 5.7.1
*/
module top();
  logic [31:0] a;

  initial begin
    a = 4af; // is illegal (hexadecimal format requires 'h)
  end

endmodule
