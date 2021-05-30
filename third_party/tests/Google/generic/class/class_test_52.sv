// Copyright (C) 2019-2021  The SymbiFlow Authors.
//
// Use of this source code is governed by a ISC-style
// license that can be found in the LICENSE file or at
// https://opensource.org/licenses/ISC
//
// SPDX-License-Identifier: ISC


/*
:name: class_test_52
:description: Test
:tags: 6.15 8.3
*/
class uvm_sequence_item;
endclass
class how_wide #(type DT=int) extends uvm_sequence_item;
  localparam Max_int = {$bits(DT) - 1{1'b1}};
  localparam Min_int = {$bits(int) - $bits(DT){1'b1}};
endclass

module test;
endmodule
