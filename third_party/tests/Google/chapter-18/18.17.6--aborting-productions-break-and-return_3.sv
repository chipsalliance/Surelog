// Copyright (C) 2019-2021  The SymbiFlow Authors.
//
// Use of this source code is governed by a ISC-style
// license that can be found in the LICENSE file or at
// https://opensource.org/licenses/ISC
//
// SPDX-License-Identifier: ISC


/*
:name: aborting_productions_break_and_return_3
:description: return statement test
:tags: uvm-random uvm
*/

import uvm_pkg::*;
`include "uvm_macros.svh"

class env extends uvm_env;
  int x;
  int return_on = 1;

  function new(string name, uvm_component parent = null);
    super.new(name, parent);
  endfunction
  
  task run_phase(uvm_phase phase);
    phase.raise_objection(this);
    begin
      randsequence( main )
        main : first second third;
        first : { x = x + 20; };
        second : { if(return_on == 1) return; x = x + 10; };
        third : { x = x + 5;};
      endsequence

      if(x == 25) begin
        `uvm_info("RESULT", $sformatf("x = %0d SUCCESS", x), UVM_LOW);
      end else begin
        `uvm_error("RESULT", $sformatf("x = %0d FAILED", x));
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
