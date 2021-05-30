// Copyright (C) 2019-2021  The SymbiFlow Authors.
//
// Use of this source code is governed by a ISC-style
// license that can be found in the LICENSE file or at
// https://opensource.org/licenses/ISC
//
// SPDX-License-Identifier: ISC


/*
:name: integers-sized-illegal
:description: Integer literal constants
:should_fail_because: illegal negative decimal syntax, proper one is -8'd6
:tags: 5.7.1
*/
module top();
  logic  [7:0] a;

  initial begin
    a = 8'd-6;
  end

endmodule
