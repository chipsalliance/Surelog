// Copyright (C) 2019-2021  The SymbiFlow Authors.
//
// Use of this source code is governed by a ISC-style
// license that can be found in the LICENSE file or at
// https://opensource.org/licenses/ISC
//
// SPDX-License-Identifier: ISC


/*
:name: set_randstate_0
:description: set_randstate() test
:tags: uvm-random uvm
*/

import uvm_pkg::*;
`include "uvm_macros.svh"

class a;
    rand int x;
endclass

class env extends uvm_env;

  a obj = new;
  string randstate;
  int prev_x;

  function new(string name, uvm_component parent = null);
    super.new(name, parent);
  endfunction
  
  task run_phase(uvm_phase phase);
    phase.raise_objection(this);
    begin
      randstate = obj.get_randstate();
      obj.randomize();
      prev_x = obj.x;
      obj.set_randstate(randstate);
      obj.randomize();

      if(obj.x == prev_x) begin
        `uvm_info("RESULT", $sformatf("obj.x = %0d prev_x = %0d SUCCESS", obj.x, prev_x), UVM_LOW);
      end else begin
        `uvm_error("RESULT", $sformatf("obj.x = %0d prev_x = %0d FAILED", obj.x, prev_x));
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
