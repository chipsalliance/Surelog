// Copyright (C) 2019-2021  The SymbiFlow Authors.
//
// Use of this source code is governed by a ISC-style
// license that can be found in the LICENSE file or at
// https://opensource.org/licenses/ISC
//
// SPDX-License-Identifier: ISC


/*
:name: in-line_constraints--randomize_0
:description: in-line constraints test - randomize()
:tags: uvm-random uvm
*/

import uvm_pkg::*;
`include "uvm_macros.svh"

class a;
    rand bit [7:0] x, y, z;
    constraint c { z == x + y; }
endclass

class env extends uvm_env;

  a obj = new;

  function new(string name, uvm_component parent = null);
    super.new(name, parent);
  endfunction
  
  task run_phase(uvm_phase phase);
    phase.raise_objection(this);
    begin
      obj.randomize() with { x < y; };
      if(obj.z == obj.x + obj.y && obj.x < obj.y) begin
        `uvm_info("RESULT", $sformatf("obj.x = %0d obj.y = %0d obj.z = %0d SUCCESS", obj.x, obj.y, obj.z), UVM_LOW);
      end else begin
        `uvm_error("RESULT", $sformatf("obj.x = %0d obj.y = %0d obj.z = %0d FAILED", obj.x, obj.y, obj.z));
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
