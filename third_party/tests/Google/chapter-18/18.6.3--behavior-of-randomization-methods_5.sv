// Copyright (C) 2019-2021  The SymbiFlow Authors.
//
// Use of this source code is governed by a ISC-style
// license that can be found in the LICENSE file or at
// https://opensource.org/licenses/ISC
//
// SPDX-License-Identifier: ISC


/*
:name: behavior_of_randomization_methods_5
:description:  behavior of randomization methods test
:should_fail_because: The randomize() method is built-in and cannot be overridden.
:tags: uvm-random uvm
:type: simulation
*/

import uvm_pkg::*;
`include "uvm_macros.svh"

class a;
    rand int b;
    constraint c { b > 5 && b < 12; }

    function void randomize();
        b = 7;
    endfunction
endclass

class env extends uvm_env;

  a obj = new;

  function new(string name, uvm_component parent = null);
    super.new(name, parent);
  endfunction
  
  task run_phase(uvm_phase phase);
    phase.raise_objection(this);
    begin
      obj.randomize();

      if(b > 5 && b < 12) begin
        `uvm_info("RESULT", $sformatf("obj.b = %0d SUCCESS", obj.b), UVM_LOW);
      end else begin
        `uvm_error("RESULT", $sformatf("obj.b = %0d FAILED", obj.b));
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
