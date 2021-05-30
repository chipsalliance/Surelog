// Copyright (C) 2019-2021  The SymbiFlow Authors.
//
// Use of this source code is governed by a ISC-style
// license that can be found in the LICENSE file or at
// https://opensource.org/licenses/ISC
//
// SPDX-License-Identifier: ISC


/*
:name: pre_randomize_method_1
:description: pre_randomize() method test
:tags: uvm-random uvm
*/

import uvm_pkg::*;
`include "uvm_macros.svh"

class a;
    rand int b;
    int d;

    constraint c { b == 5; }
    function void pre_randomize();
        d = 20;
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
      if(obj.b == 5 && obj.d == 20) begin
        `uvm_info("RESULT", $sformatf("obj.b = %0d obj.d = %0d SUCCESS", obj.b, obj.d), UVM_LOW);
      end else begin
        `uvm_error("RESULT", $sformatf("obj.b = %0d obj.d = %0d FAILED", obj.b, obj.d));
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
