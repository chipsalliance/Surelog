// Copyright (C) 2019-2021  The SymbiFlow Authors.
//
// Use of this source code is governed by a ISC-style
// license that can be found in the LICENSE file or at
// https://opensource.org/licenses/ISC
//
// SPDX-License-Identifier: ISC


/*
:name: controlling-constraints-with-constraint_mode_2
:description: constraint_mode() test
:should_fail_because: The constraint_mode() method is built-in and cannot be overridden.
:tags: uvm-random uvm
:type: simulation
*/

import uvm_pkg::*;
`include "uvm_macros.svh"

class a;
    rand int x;
    function int constraint_mode();
        return 1;
    endfunction
endclass

class env extends uvm_env;

  a obj = new;
  int ret;

  function new(string name, uvm_component parent = null);
    super.new(name, parent);
  endfunction
  
  task run_phase(uvm_phase phase);
    phase.raise_objection(this);
    begin
      ret = obj.constraint_mode();

      if(ret == 1) begin
        `uvm_info("RESULT", $sformatf("ret = %0d SUCCESS", ret), UVM_LOW);
      end else begin
        `uvm_error("RESULT", $sformatf("ret = %0d FAILED", ret));
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
