// Copyright (C) 2019-2021  The SymbiFlow Authors.
//
// Use of this source code is governed by a ISC-style
// license that can be found in the LICENSE file or at
// https://opensource.org/licenses/ISC
//
// SPDX-License-Identifier: ISC


/*
:name: behavior_of_randomization_methods_2
:description: If randomize() fails, the constraints are infeasible, and the random variables retain their previous values.
:tags: uvm-random uvm
*/

import uvm_pkg::*;
`include "uvm_macros.svh"

class a;
    rand int b = 1;

    /* Create infeasible constraint */
    constraint c { b == 0 && b > 0; }
endclass

class env extends uvm_env;

  a obj = new;
  int prev_value, status;

  function new(string name, uvm_component parent = null);
    super.new(name, parent);
  endfunction
  
  task run_phase(uvm_phase phase);
    phase.raise_objection(this);
    begin
      prev_value = obj.b;
      status = obj.randomize();

      if(status == 0 && prev_value == obj.b) begin
        `uvm_info("RESULT", $sformatf("obj.b = %0d prev_value = %0d SUCCESS", obj.b, prev_value), UVM_LOW);
      end else begin
        `uvm_error("RESULT", $sformatf("obj.b = %0d prev_value = %0d FAILED", obj.b, prev_value));
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
