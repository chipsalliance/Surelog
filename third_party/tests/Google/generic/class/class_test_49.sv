// Copyright (C) 2019-2021  The SymbiFlow Authors.
//
// Use of this source code is governed by a ISC-style
// license that can be found in the LICENSE file or at
// https://opensource.org/licenses/ISC
//
// SPDX-License-Identifier: ISC


/*
:name: class_test_49
:description: Test
:tags: 6.15 8.3
*/

package glb;
  localparam int arr[3] = '{1,2,3};
endpackage

function int f(int a);
  return a;
endfunction

class params_as_class_item;
  parameter N = 2;
  parameter reg P = '1;
  localparam M = f(glb::arr[N]) + 1;
endclass

module test;
endmodule
