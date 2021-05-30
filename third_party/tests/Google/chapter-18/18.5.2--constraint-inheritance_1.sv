// Copyright (C) 2019-2021  The SymbiFlow Authors.
//
// Use of this source code is governed by a ISC-style
// license that can be found in the LICENSE file or at
// https://opensource.org/licenses/ISC
//
// SPDX-License-Identifier: ISC


/*
:name: constraint_inheritance_1
:description: contraint inheritance test
:tags: uvm-random uvm
*/

import uvm_pkg::*;
`include "uvm_macros.svh"

class a;
    rand int b;
    constraint c { b == 5; };
endclass

class a2 extends a;
    rand int b2;
    constraint c2 { b2 == b; }
endclass

class env extends uvm_env;

  a2 obj = new;

  function new(string name, uvm_component parent = null);
    super.new(name, parent);
  endfunction
  
  task run_phase(uvm_phase phase);
    phase.raise_objection(this);
    begin
      obj.randomize();
      if(obj.b2 == 5) begin
        `uvm_info("RESULT", $sformatf("b2 = %0d SUCCESS", obj.b2), UVM_LOW);
      end else begin
        `uvm_error("RESULT", $sformatf("b2 = %0d FAILED", obj.b2));
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
