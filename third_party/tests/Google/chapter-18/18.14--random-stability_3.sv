// Copyright (C) 2019-2021  The SymbiFlow Authors.
//
// Use of this source code is governed by a ISC-style
// license that can be found in the LICENSE file or at
// https://opensource.org/licenses/ISC
//
// SPDX-License-Identifier: ISC


/*
:name: random_stability_3
:description: random stability - randcase test
:tags: uvm-random uvm
*/

import uvm_pkg::*;
`include "uvm_macros.svh"

class env extends uvm_env;
  process p;
  string randstate;
  int x, y;

  function new(string name, uvm_component parent = null);
    super.new(name, parent);
  endfunction
  
  task run_phase(uvm_phase phase);
    phase.raise_objection(this);
    begin
      p = process::self();
      randstate = p.get_randstate();
      randcase
          2 : x = 1;
          2 : x = 2;
          2 : x = 3;
          2 : x = 4;
          2 : x = 5;
      endcase

      p.set_randstate(randstate);
      randcase
          2 : y = 1;
          2 : y = 2;
          2 : y = 3;
          2 : y = 4;
          2 : y = 5;
      endcase

      if(x == y) begin
        `uvm_info("RESULT", $sformatf("x = %0d y = %0d SUCCESS", x, y), UVM_LOW);
      end else begin
        `uvm_error("RESULT", $sformatf("x = %0d y = %0d FAILED", x, y));
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
