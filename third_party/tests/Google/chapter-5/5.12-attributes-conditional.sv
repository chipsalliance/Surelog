// Copyright (C) 2019-2021  The SymbiFlow Authors.
//
// Use of this source code is governed by a ISC-style
// license that can be found in the LICENSE file or at
// https://opensource.org/licenses/ISC
//
// SPDX-License-Identifier: ISC


/*
:name: attributes-conditional
:description: Assing attributes to a conditional operator
:tags: 5.12
*/

module top();
  bit a, b, c, d;

  initial begin;
    a = b ? (* no_glitch *) c : d;
  end

endmodule
