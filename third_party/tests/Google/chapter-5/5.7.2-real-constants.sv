// Copyright (C) 2019-2021  The SymbiFlow Authors.
//
// Use of this source code is governed by a ISC-style
// license that can be found in the LICENSE file or at
// https://opensource.org/licenses/ISC
//
// SPDX-License-Identifier: ISC


/*
:name: real-constants
:description: Examples of real literal constants
:tags: 5.7.2
*/
module top();
  logic [31:0] a;

  initial begin;
    a = 1.2;
    a = 0.1;
    a = 2394.26331;
    a = 1.2E12;           // the exponent symbol can be e or E
    a = 1.30e-2;
    a = 0.1e-0;
    a = 23E10;
    a = 29E-2;
    a = 236.123_763_e-12; // underscores are ignored
  end

endmodule
