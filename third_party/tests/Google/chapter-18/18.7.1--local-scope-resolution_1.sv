// Copyright (C) 2019-2021  The SymbiFlow Authors.
//
// Use of this source code is governed by a ISC-style
// license that can be found in the LICENSE file or at
// https://opensource.org/licenses/ISC
//
// SPDX-License-Identifier: ISC


/*
:name: local_scope_resolution_1
:description: local:: scope resolution test
:tags: uvm-random uvm
*/

import uvm_pkg::*;
`include "uvm_macros.svh"

class a;
    rand int x;
endclass

function int F(a obj, int x);
    F = obj.randomize() with {x > 0; x < local::x; };
endfunction

class env extends uvm_env;

  a obj = new;
  int x;

  function new(string name, uvm_component parent = null);
    super.new(name, parent);
  endfunction
  
  task run_phase(uvm_phase phase);
    phase.raise_objection(this);
    begin
      x = 10;
      F(obj, x);
      if(obj.x < x) begin
        `uvm_info("RESULT", $sformatf("obj.x = %0d x = %0d SUCCESS", obj.x, x), UVM_LOW);
      end else begin
        `uvm_error("RESULT", $sformatf("obj.x = %0d x = %0d FAILED", obj.x, x));
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
