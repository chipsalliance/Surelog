// Copyright (C) 2019-2021  The SymbiFlow Authors.
//
// Use of this source code is governed by a ISC-style
// license that can be found in the LICENSE file or at
// https://opensource.org/licenses/ISC
//
// SPDX-License-Identifier: ISC


/*
:name: controlling-constraints-with-constraint_mode_0
:description: constraint_mode() test
:tags: uvm-random uvm
*/

import uvm_pkg::*;
`include "uvm_macros.svh"

class a;
    rand int x;
    constraint c1 { x < 0; }
    constraint c2 { x > 0; }
endclass

class env extends uvm_env;

  a obj = new;
  int ret1, ret2;

  function new(string name, uvm_component parent = null);
    super.new(name, parent);
  endfunction
  
  task run_phase(uvm_phase phase);
    phase.raise_objection(this);
    begin
      obj.c1.constraint_mode(0);
      ret1 = obj.c1.constraint_mode();
      ret2 = obj.c2.constraint_mode();
      obj.randomize();
      if(obj.x > 0 && ret1 == 0 && ret2 == 1) begin
        `uvm_info("RESULT", $sformatf("ret1 = %0d ret2 = %0d SUCCESS", ret1, ret2), UVM_LOW);
      end else begin
        `uvm_error("RESULT", $sformatf("ret1 = %0d ret2 = %0d FAILED", ret1, ret2));
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
