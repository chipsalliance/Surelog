// Copyright (C) 2019-2021  The SymbiFlow Authors.
//
// Use of this source code is governed by a ISC-style
// license that can be found in the LICENSE file or at
// https://opensource.org/licenses/ISC
//
// SPDX-License-Identifier: ISC


/*
:name: uvm_test_run_test
:description: test if uvm_test instance can be called by name
:tags: uvm uvm-classes
:type: simulation parsing
*/

import uvm_pkg::*;
`include "uvm_macros.svh"

class simple_test extends uvm_test;
    `uvm_component_utils(simple_test)

    function new(string name, uvm_component parent = null);
      super.new(name, parent);
    endfunction

    virtual function void connect_phase(uvm_phase phase);
        super.connect_phase(phase);
    endfunction

    virtual function void build_phase(uvm_phase phase);
        super.build_phase(phase);
    endfunction

    task run_phase(uvm_phase phase);
        phase.raise_objection(this);
        `uvm_info("RESULT", "SUCCESS, simple_test called", UVM_LOW);
        phase.drop_objection(this);
    endtask
endclass

module top;
    initial begin
        run_test("simple_test");
    end
endmodule
