// Copyright (C) 2019-2021  The SymbiFlow Authors.
//
// Use of this source code is governed by a ISC-style
// license that can be found in the LICENSE file or at
// https://opensource.org/licenses/ISC
//
// SPDX-License-Identifier: ISC


/*
:name: class_member_test_27
:description: Test
:tags: 8.3
*/
class report_server; endclass
typedef int uvm_phase;

class myclass;
virtual function void starter(uvm_phase phase);
  report_server new_server = new;
endfunction : starter
endclass

module test;
endmodule
