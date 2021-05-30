// Copyright (C) 2019-2021  The SymbiFlow Authors.
//
// Use of this source code is governed by a ISC-style
// license that can be found in the LICENSE file or at
// https://opensource.org/licenses/ISC
//
// SPDX-License-Identifier: ISC


/*
:name: random_stability_1
:description: random stability - shuffle test
:tags: uvm-random uvm
*/

import uvm_pkg::*;
`include "uvm_macros.svh"

class env extends uvm_env;
  int tab1[5] = { 1, 2, 3, 4, 5 };
  int tab2[5] = { 1, 2, 3, 4, 5 };
  process p;
  string randstate;

  function new(string name, uvm_component parent = null);
    super.new(name, parent);
  endfunction
  
  task run_phase(uvm_phase phase);
    phase.raise_objection(this);
    begin
      p = process::self();
      randstate = p.get_randstate();
      tab1.shuffle;
      p.set_randstate(randstate);
      tab2.shuffle;

      if(tab1 == tab2) begin
        `uvm_info("RESULT", $sformatf("tab1 = %p tab2 = %p SUCCESS", tab1, tab2), UVM_LOW);
      end else begin
        `uvm_error("RESULT", $sformatf("tab1 = %p tab2 = %p FAILED", tab1, tab2));
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
