// Copyright (C) 2019-2021  The SymbiFlow Authors.
//
// Use of this source code is governed by a ISC-style
// license that can be found in the LICENSE file or at
// https://opensource.org/licenses/ISC
//
// SPDX-License-Identifier: ISC


/*
:name: class_test_26
:description: Test
:tags: 6.15 8.3
*/
interface class Bar #(parameter N); endclass

parameter int N = 1;
class Foo implements Bar#(N); endclass

module test;
endmodule
