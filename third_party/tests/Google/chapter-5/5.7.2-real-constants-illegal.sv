// Copyright (C) 2019-2021  The SymbiFlow Authors.
//
// Use of this source code is governed by a ISC-style
// license that can be found in the LICENSE file or at
// https://opensource.org/licenses/ISC
//
// SPDX-License-Identifier: ISC


/*
:name: real-constants-illegal
:description: Examples of real literal constants
:should_fail_because: Real literal constants must have at least one digit on each side of the decimal point
:tags: 5.7.2
*/
module top();
  logic [31:0] a;

  initial begin;
    a = .12;
    a = 9.;
    a = 4.E3;
    a = .2e-7;
  end

endmodule
