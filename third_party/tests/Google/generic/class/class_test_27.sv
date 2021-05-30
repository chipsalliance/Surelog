// Copyright (C) 2019-2021  The SymbiFlow Authors.
//
// Use of this source code is governed by a ISC-style
// license that can be found in the LICENSE file or at
// https://opensource.org/licenses/ISC
//
// SPDX-License-Identifier: ISC


/*
:name: class_test_27
:description: Test
:tags: 6.15 8.3
*/

package Package;
  interface class Bar #(parameter A, B); endclass
endpackage

class Foo implements Package::Bar#(1, 2); endclass

module test;
endmodule
