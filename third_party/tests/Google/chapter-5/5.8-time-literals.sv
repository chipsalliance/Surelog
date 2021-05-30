// Copyright (C) 2019-2021  The SymbiFlow Authors.
//
// Use of this source code is governed by a ISC-style
// license that can be found in the LICENSE file or at
// https://opensource.org/licenses/ISC
//
// SPDX-License-Identifier: ISC


/*
:name: time-literals
:description: Examples of time literals
:tags: 5.8
*/

`timescale 100ps/10ps

module top();
  time a;

  initial begin
    a = 1fs;
    a = 1ps;
    a = 1ns;
    a = 1us;
    a = 1ms;
    a = 1s;

    /* real */
    a = 2.1ms;

  end;

endmodule
