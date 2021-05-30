// Copyright (C) 2019-2021  The SymbiFlow Authors.
//
// Use of this source code is governed by a ISC-style
// license that can be found in the LICENSE file or at
// https://opensource.org/licenses/ISC
//
// SPDX-License-Identifier: ISC


/*
:name: soft_constraint_priorities_4
:description: soft constraint priorities test
:tags: uvm-random uvm
*/

import uvm_pkg::*;
`include "uvm_macros.svh"

class a1;
    rand int b;

    constraint c1 {
        soft b > 4;
        soft b < 12; }
endclass

class a2 extends a1;

    constraint c2 {soft b == 20; }
    constraint c3;
endclass

constraint a2::c3 { soft b > 100; };

class env extends uvm_env;

  a2 obj = new;

  function new(string name, uvm_component parent = null);
    super.new(name, parent);
  endfunction
  
  task run_phase(uvm_phase phase);
    phase.raise_objection(this);
    begin
      obj.randomize() with { soft b == 90; };
      if(obj.b == 90) begin
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
