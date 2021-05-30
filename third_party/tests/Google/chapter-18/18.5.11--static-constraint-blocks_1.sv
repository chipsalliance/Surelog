// Copyright (C) 2019-2021  The SymbiFlow Authors.
//
// Use of this source code is governed by a ISC-style
// license that can be found in the LICENSE file or at
// https://opensource.org/licenses/ISC
//
// SPDX-License-Identifier: ISC


/*
:name: static_constraint_blocks_1
:description: static constraint blocks test
:tags: uvm-random uvm
*/

import uvm_pkg::*;
`include "uvm_macros.svh"

class a;
    rand int b;

    static constraint c1 { b == 5; }
    static constraint c2 { b == 2; }
endclass

class env extends uvm_env;

  a obj1 = new;
  a obj2 = new;

  function new(string name, uvm_component parent = null);
    super.new(name, parent);
    /* shall affect all instances of constraint c2 */
    obj1.c1.constraint_mode(0);
  endfunction

  task run_phase(uvm_phase phase);
    phase.raise_objection(this);
    begin
      obj1.randomize();
      obj2.randomize();
      if(obj1.b == 2 && obj2.b == 2) begin
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
