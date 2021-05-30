// Copyright (C) 2019-2021  The SymbiFlow Authors.
//
// Use of this source code is governed by a ISC-style
// license that can be found in the LICENSE file or at
// https://opensource.org/licenses/ISC
//
// SPDX-License-Identifier: ISC


/*
:name: in-line_constraints--randomize_6
:description: in-line constraints test - randomize()
:tags: uvm-random uvm
*/

import uvm_pkg::*;
`include "uvm_macros.svh"

class a;
    rand int x;
    int y = -1;
endclass

function int F(a obj, int y);
    F = obj.randomize() with (x) { x > 0; x < y; };
endfunction

class env extends uvm_env;

  a obj = new;
  int y;

  function new(string name, uvm_component parent = null);
    super.new(name, parent);
  endfunction
  
  task run_phase(uvm_phase phase);
    phase.raise_objection(this);
    begin
      y = 10;
      F(obj, y);
      if(obj.x > 0 && obj.x < y) begin
        `uvm_info("RESULT", $sformatf("obj.x = %0d y = %0d SUCCESS", obj.x, y), UVM_LOW);
      end else begin
        `uvm_error("RESULT", $sformatf("obj.x = %0d y = %0d FAILED", obj.x, y));
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
