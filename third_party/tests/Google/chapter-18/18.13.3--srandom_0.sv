// Copyright (C) 2019-2021  The SymbiFlow Authors.
//
// Use of this source code is governed by a ISC-style
// license that can be found in the LICENSE file or at
// https://opensource.org/licenses/ISC
//
// SPDX-License-Identifier: ISC


/*
:name: srandom_0
:description: srandom() test
:tags: uvm-random uvm
*/

import uvm_pkg::*;
`include "uvm_macros.svh"

class a;
    rand int x;
    constraint c {x > 0 && x < 30;};
endclass

class env extends uvm_env;

  a obj = new;
  int ret1, ret2, prev_x, seed = 20;

  function new(string name, uvm_component parent = null);
    super.new(name, parent);
  endfunction
  
  task run_phase(uvm_phase phase);
    phase.raise_objection(this);
    begin
      obj.srandom(seed);
      ret1 = obj.randomize();
      prev_x = obj.x;
      obj.srandom(seed);
      ret2 = obj.randomize();
      if(ret1 == 1 && ret2 == 1 && obj.x > 0 && obj.x < 30 && prev_x == obj.x) begin
        `uvm_info("RESULT", $sformatf("prev_x = %0d obj.x = %0d SUCCESS", prev_x, obj.x), UVM_LOW);
      end else begin
        `uvm_error("RESULT", $sformatf("prev_x = %0d obj.x = %0d FAILED", prev_x, obj.x));
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
