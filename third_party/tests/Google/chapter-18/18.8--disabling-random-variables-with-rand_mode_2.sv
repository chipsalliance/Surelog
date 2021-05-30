// Copyright (C) 2019-2021  The SymbiFlow Authors.
//
// Use of this source code is governed by a ISC-style
// license that can be found in the LICENSE file or at
// https://opensource.org/licenses/ISC
//
// SPDX-License-Identifier: ISC


/*
:name: disabling-random-variables-with-rand_mode_2
:description: rand_mode() test
:tags: uvm-random uvm
*/

import uvm_pkg::*;
`include "uvm_macros.svh"

class a;
    rand int x, y;
    constraint c {x > 0; x < 12; }
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
      obj.rand_mode(0);
      obj.x.rand_mode(1);
      ret1 = obj.x.rand_mode();
      ret2 = obj.randomize();
      if(ret1 == 1 && ret2 == 1 && obj.x > 0 && obj.x < 12) begin
        `uvm_info("RESULT", $sformatf("ret1 = %0d ret2 = %0d obj.x = %0d SUCCESS", ret1, ret2, obj.x), UVM_LOW);
      end else begin
        `uvm_error("RESULT", $sformatf("ret1 = %0d ret2 = %0d obj.x = %0d FAILED", ret1, ret2, obj.x));
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
