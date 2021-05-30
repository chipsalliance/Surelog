// Copyright (C) 2019-2021  The SymbiFlow Authors.
//
// Use of this source code is governed by a ISC-style
// license that can be found in the LICENSE file or at
// https://opensource.org/licenses/ISC
//
// SPDX-License-Identifier: ISC


/*
:name: integers-left-padding-bit
:description: Automatic left padding of literal numbers using single-bit value
:tags: 5.7.1
*/
module top();
  logic [15:0] a, b, c, d;

  initial begin;
    a = '0; // sets all 16 bits to 0
    b = '1; // sets all 16 bits to 1
    c = 'x; // sets all 16 bits to x
    d = 'z; // sets all 16 bits to z
  end

endmodule
