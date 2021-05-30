// Copyright (C) 2019-2021  The SymbiFlow Authors.
//
// Use of this source code is governed by a ISC-style
// license that can be found in the LICENSE file or at
// https://opensource.org/licenses/ISC
//
// SPDX-License-Identifier: ISC


/*
:name: super-def-new
:description: Base class has no user-defined constructor, derived class accesses superclass new()
:tags: 8.15
*/
package test_pkg;

  virtual class uvm_void;
  endclass : uvm_void

  class uvm_object extends uvm_void;
    virtual function void print ();
      $display ("Print");
    endfunction : print 
  endclass : uvm_object

  class uvm_report_object extends uvm_object;
    function new ();
      super.new ();
    endfunction : new 
  endclass : uvm_report_object 

endpackage : test_pkg

module m;
  import test_pkg::*;
  uvm_object u0;
  
   initial begin : test
     #100;
     $display ("Hello World");
     u0 = new ();
     u0.print();

   end : test

endmodule : m

