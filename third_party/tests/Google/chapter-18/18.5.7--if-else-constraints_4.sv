// Copyright (C) 2019-2021  The SymbiFlow Authors.
//
// Use of this source code is governed by a ISC-style
// license that can be found in the LICENSE file or at
// https://opensource.org/licenses/ISC
//
// SPDX-License-Identifier: ISC


/*
:name: if_else_constraints_4
:description: if-else constraints test
:tags: uvm-random uvm
*/

import uvm_pkg::*;
`include "uvm_macros.svh"

class a;
    rand int b1, b2, b3;
    constraint c1 { b1 == 5; }
    constraint c2 { b2 == 3; }
    constraint c3 { if (b1 == 5)
                      if (b2 == 2) b3 == 4; 
                      else b3 == 10;}
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
      if(obj.b3 == 10) begin
        `uvm_info("RESULT", $sformatf("b3 = %0d SUCCESS", obj.b3), UVM_LOW);
      end else begin
        `uvm_error("RESULT", $sformatf("b3 = %0d FAILED", obj.b3));
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
