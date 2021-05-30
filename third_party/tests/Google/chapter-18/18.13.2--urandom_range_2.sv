// Copyright (C) 2019-2021  The SymbiFlow Authors.
//
// Use of this source code is governed by a ISC-style
// license that can be found in the LICENSE file or at
// https://opensource.org/licenses/ISC
//
// SPDX-License-Identifier: ISC


/*
:name: urandom_range_2
:description: urandom_range() test
:tags: uvm-random uvm
*/

import uvm_pkg::*;
`include "uvm_macros.svh"

class a;
    function int unsigned do_urandom_range(int unsigned maxval, int unsigned minval);
        int unsigned val;
        val = $urandom_range(maxval, minval);
        return val;
    endfunction
endclass

class env extends uvm_env;

  a obj = new;
  int unsigned max = 10, min = 1, ret;

  function new(string name, uvm_component parent = null);
    super.new(name, parent);
  endfunction
  
  task run_phase(uvm_phase phase);
    phase.raise_objection(this);
    begin
      /* If max is less than min, then arguments should be automatically reversed */
      ret = obj.do_urandom_range(min, max);
      if(ret >= min && ret <= max) begin
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
