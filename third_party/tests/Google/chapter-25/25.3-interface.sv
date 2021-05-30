// Copyright (C) 2019-2021  The SymbiFlow Authors.
//
// Use of this source code is governed by a ISC-style
// license that can be found in the LICENSE file or at
// https://opensource.org/licenses/ISC
//
// SPDX-License-Identifier: ISC


/*
:name: interface
:description: interface test
:tags: 25.3
*/

interface test_bus;
  logic test_pad;
endinterface: test_bus

module sub(test_bus iface);
endmodule

module top;
   test_bus iface();
   sub sub (.iface);
endmodule
