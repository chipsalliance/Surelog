// Copyright (C) 2019-2021  The SymbiFlow Authors.
//
// Use of this source code is governed by a ISC-style
// license that can be found in the LICENSE file or at
// https://opensource.org/licenses/ISC
//
// SPDX-License-Identifier: ISC


/*
:name: class_test_30
:description: Test
:tags: 6.15 8.3
*/
class Foo;
integer size;
function new (integer size);
  begin
    this.size = size;
  end
endfunction
task print();
  begin
    $write("Hello, world!");
  end
endtask
endclass

module test;
endmodule
