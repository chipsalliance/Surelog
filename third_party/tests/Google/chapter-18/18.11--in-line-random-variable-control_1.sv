// Copyright (C) 2019-2021  The SymbiFlow Authors.
//
// Use of this source code is governed by a ISC-style
// license that can be found in the LICENSE file or at
// https://opensource.org/licenses/ISC
//
// SPDX-License-Identifier: ISC


/*
:name: in-line_random_variable-control_1
:description: in-line random variable control test
:tags: uvm-random uvm
*/

import uvm_pkg::*;
`include "uvm_macros.svh"

class a;
    randc bit [7:0] x = 0, y = 0;
    bit [7:0] v = 0, w = 0;
    constraint c { x < v && y > w; };
endclass


class env extends uvm_env;

  a obj = new;

  function new(string name, uvm_component parent = null);
    super.new(name, parent);
  endfunction
  
  task run_phase(uvm_phase phase);
    phase.raise_objection(this);
    begin
      /* random variables: v, w state variables: x, y */
      obj.randomize(v, w);

      if(obj.x == 0 && obj.y == 0) begin
        `uvm_info("RESULT", $sformatf("obj.x = %0d obj.v = %0d obj.y = %0d obj.w = %0d SUCCESS", obj.x, obj.v, obj.y, obj.w), UVM_LOW);
      end else begin
        `uvm_error("RESULT", $sformatf("obj.x = %0d obj.v = %0d obj.y = %0d obj.w = %0d FAILED", obj.x, obj.v, obj.y, obj.w));
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
