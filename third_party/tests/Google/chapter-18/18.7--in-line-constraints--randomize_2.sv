// Copyright (C) 2019-2021  The SymbiFlow Authors.
//
// Use of this source code is governed by a ISC-style
// license that can be found in the LICENSE file or at
// https://opensource.org/licenses/ISC
//
// SPDX-License-Identifier: ISC


/*
:name: in-line_constraints--randomize_2
:description: in-line constraints test - randomize()
:tags: uvm-random uvm
*/

import uvm_pkg::*;
`include "uvm_macros.svh"

class a1;
    rand int x;
endclass

class a2;
    int x, y;

    task do_randomize(a1 obj, int x, int z);
        int result;
        /* In the line below x should be a member of class a1 */
        result = obj.randomize() with {x > 0; x < y + z;};
    endtask
endclass

class env extends uvm_env;

  a1 obj1 = new;
  a2 obj2 = new;
  int z;

  function new(string name, uvm_component parent = null);
    super.new(name, parent);
  endfunction
  
  task run_phase(uvm_phase phase);
    phase.raise_objection(this);
    begin
      obj2.x = -20;
      obj2.y = 5;
      z = 10;
      obj2.do_randomize(obj1, -20, z);
      if(obj1.x > 0 && obj1.x < obj2.y + z) begin
        `uvm_info("RESULT", $sformatf("obj1.x = %0d obj2.x = %0d obj2.y = %0d SUCCESS", obj1.x, obj2.x, obj2.y), UVM_LOW);
      end else begin
        `uvm_error("RESULT", $sformatf("obj1.x = %0d obj2.x = %0d obj2.y = %0d FAILED", obj1.x, obj2.x, obj2.y));
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
