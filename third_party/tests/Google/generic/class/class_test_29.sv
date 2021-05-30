// Copyright (C) 2019-2021  The SymbiFlow Authors.
//
// Use of this source code is governed by a ISC-style
// license that can be found in the LICENSE file or at
// https://opensource.org/licenses/ISC
//
// SPDX-License-Identifier: ISC


/*
:name: class_test_29
:description: Test
:tags: 6.15 8.3
*/

package Pkg;
  interface class Bar; endclass
endpackage

class Base; endclass
interface class Baz; endclass

class Foo extends Base implements Pkg::Bar, Baz; endclass

module test;
endmodule
