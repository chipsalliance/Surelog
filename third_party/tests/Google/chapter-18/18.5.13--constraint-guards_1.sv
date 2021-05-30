// Copyright (C) 2019-2021  The SymbiFlow Authors.
//
// Use of this source code is governed by a ISC-style
// license that can be found in the LICENSE file or at
// https://opensource.org/licenses/ISC
//
// SPDX-License-Identifier: ISC


/*
:name: constraint_guards_1
:description: constraint guards test
:tags: uvm-random uvm
*/

import uvm_pkg::*;
`include "uvm_macros.svh"

class b;
    int d1;
endclass

class a;
    rand int b1;
    b next;

    constraint c1 { if (next == null) b1 == 5; }
endclass

class env extends uvm_env;

  a obj1 = new;

  function new(string name, uvm_component parent = null);
    super.new(name, parent);
  endfunction
  
  task run_phase(uvm_phase phase);
    phase.raise_objection(this);
    begin
      obj1.randomize();
      if(obj1.b1 == 5) begin
        `uvm_info("RESULT", $sformatf("obj1.b1 = %0d SUCCESS", obj1.b1), UVM_LOW);
      end else begin
        `uvm_error("RESULT", $sformatf("obj1.b1 = %0d FAILED", obj1.b1));
      end
    end
    phase.drop_objection(this);
  endtask: run_phase
  
endclass

module top;

  env environment;

  initial begin
    environment = new("env");
    run_test();
  end
  
endmodule
