// Copyright (C) 2019-2021  The SymbiFlow Authors.
//
// Use of this source code is governed by a ISC-style
// license that can be found in the LICENSE file or at
// https://opensource.org/licenses/ISC
//
// SPDX-License-Identifier: ISC


/*
:name: thread_stability_0
:description: thread stability test
:tags: uvm-random uvm
*/

import uvm_pkg::*;
`include "uvm_macros.svh"

class env extends uvm_env;
  int unsigned val1, val2;
  process p1, p2;

  function new(string name, uvm_component parent = null);
    super.new(name, parent);
  endfunction
  
  task run_phase(uvm_phase phase);
    phase.raise_objection(this);
    begin

      fork
        begin
            p1 = process::self();
            p1.srandom(100);
            val1 = $urandom;
        end
        begin
            p2 = process::self();
            p2.srandom(100);
            val2 = $urandom;
        end
      join

      if(val1 == val2) begin
        `uvm_info("RESULT", $sformatf("val1 = %0d val2 = %0d SUCCESS", val1, val2), UVM_LOW);
      end else begin
        `uvm_error("RESULT", $sformatf("val1 = %0d val2 = %0d FAILED", val1, val2));
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
