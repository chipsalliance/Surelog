// Copyright (C) 2019-2021  The SymbiFlow Authors.
//
// Use of this source code is governed by a ISC-style
// license that can be found in the LICENSE file or at
// https://opensource.org/licenses/ISC
//
// SPDX-License-Identifier: ISC


/*
:name: get_randstate_0
:description: get_randstate() test
:tags: uvm-random uvm
*/

import uvm_pkg::*;
`include "uvm_macros.svh"

class a;
    rand int x;
endclass

class env extends uvm_env;

  a obj = new;
  string randstate;
  int ret;

  function new(string name, uvm_component parent = null);
    super.new(name, parent);
  endfunction

  task run_phase(uvm_phase phase);
    phase.raise_objection(this);
    begin
      ret = obj.randomize();
      randstate = obj.get_randstate();

      if(ret == 1 && randstate != "") begin
        `uvm_info("RESULT", $sformatf("ret = %0d randstate = %s SUCCESS", ret, randstate), UVM_LOW);
      end else begin
        `uvm_error("RESULT", $sformatf("ret = %0d randstate = %s FAILED", ret, randstate));
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
