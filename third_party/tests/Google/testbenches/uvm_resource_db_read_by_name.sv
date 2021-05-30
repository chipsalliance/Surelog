// Copyright (C) 2019-2021  The SymbiFlow Authors.
//
// Use of this source code is governed by a ISC-style
// license that can be found in the LICENSE file or at
// https://opensource.org/licenses/ISC
//
// SPDX-License-Identifier: ISC


/*
:name: uvm_resource_db_read_by_name
:description: uvm resource_db::read_by_name test
:tags: uvm
:type: simulation parsing
*/

import uvm_pkg::*;
`include "uvm_macros.svh"

class C;
endclass

class env extends uvm_env;
    C obj;

    `uvm_component_utils(env)

    function new(string name, uvm_component parent = null);
        super.new(name, parent);
    endfunction

    virtual function void build_phase(uvm_phase phase);
        super.build_phase(phase);
    endfunction

    virtual function void connect_phase(uvm_phase phase);
        super.connect_phase(phase);
        if(uvm_resource_db#(C)::read_by_name(
            get_full_name(), "obj", obj)) begin
            `uvm_info("RESULT", "read_by_name successful", UVM_LOW);
        end
        else begin
            `uvm_error("RESULT", "read_by_name failed");
        end
    endfunction

    virtual function void end_of_elaboration_phase(uvm_phase phase);
        super.end_of_elaboration_phase(phase);
    endfunction

    task run_phase(uvm_phase phase);
        phase.raise_objection(this);
        phase.drop_objection(this);
    endtask
  
endclass

module top;
    env environment;
    C obj;

    initial begin
        environment = new("env");
        uvm_resource_db#(C)::set("env", "obj", obj);
        run_test();
    end
endmodule
