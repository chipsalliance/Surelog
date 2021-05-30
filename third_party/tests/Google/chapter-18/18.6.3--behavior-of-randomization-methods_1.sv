// Copyright (C) 2019-2021  The SymbiFlow Authors.
//
// Use of this source code is governed by a ISC-style
// license that can be found in the LICENSE file or at
// https://opensource.org/licenses/ISC
//
// SPDX-License-Identifier: ISC


/*
:name: behavior_of_randomization_methods_1
:description: static random variables test
:tags: uvm-random uvm
*/

import uvm_pkg::*;
`include "uvm_macros.svh"

class a;
    static rand int b;
    constraint c { b > 5; b < 12; }
endclass

class env extends uvm_env;

  a obj1 = new;
  a obj2 = new;

  function new(string name, uvm_component parent = null);
    super.new(name, parent);
  endfunction
  
  task run_phase(uvm_phase phase);
    phase.raise_objection(this);
    begin
      obj1.randomize();
      if(obj1.b == obj2.b) begin
        `uvm_info("RESULT", $sformatf("obj1.b = %0d obj2.b = %0d SUCCESS", obj1.b, obj2.b), UVM_LOW);
      end else begin
        `uvm_error("RESULT", $sformatf("obj1.b = %0d obj2.b = %0d FAILED", obj1.b, obj2.b));
      end

      obj2.randomize();
      if(obj1.b == obj2.b) begin
        `uvm_info("RESULT", $sformatf("obj1.b = %0d obj2.b = %0d SUCCESS", obj1.b, obj2.b), UVM_LOW);
      end else begin
        `uvm_error("RESULT", $sformatf("obj1.b = %0d obj2.b = %0d FAILED", obj1.b, obj2.b));
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
