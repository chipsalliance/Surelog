// Copyright (C) 2019-2021  The SymbiFlow Authors.
//
// Use of this source code is governed by a ISC-style
// license that can be found in the LICENSE file or at
// https://opensource.org/licenses/ISC
//
// SPDX-License-Identifier: ISC


/*
:name: assert_final_test_uvm
:description: assert final test with UVM
:type: simulation parsing
:tags: uvm uvm-assertions
:timeout: 60
*/

import uvm_pkg::*;
`include "uvm_macros.svh"

module inverter (
    input [7:0] a,
    output [7:0] b
);

    assign b = !a;

endmodule: inverter

interface inverter_if(
    output reg [7:0] a,
    input [7:0] b
);

endinterface: inverter_if

string label = "ASSERT_FINAL_UVM";

class env extends uvm_env;
    virtual inverter_if m_if;

    function new(string name, uvm_component parent = null);
        super.new(name, parent);
    endfunction

    function void connect_phase(uvm_phase phase);
        `uvm_info(label, "Started connect phase", UVM_LOW);
        assert(uvm_resource_db#(virtual inverter_if)::read_by_name(
            get_full_name(), "inverter_if", m_if));
        `uvm_info(label, "Finished connect phase", UVM_LOW);
    endfunction: connect_phase

    task run_phase(uvm_phase phase);
        phase.raise_objection(this);
        `uvm_info(label, "Started run phase", UVM_LOW);
        begin
            int a = 8'h35;
            m_if.a <= a;

            assert final (m_if.a != m_if.b) else `uvm_error(label, $sformatf("assert failed :assert: (False)"));
        end
        `uvm_info(label, "Finished run phase", UVM_LOW);
        phase.drop_objection(this);
    endtask: run_phase
endclass

module top;
    env environment;

    inverter_if dif();

    inverter dut(.a(dif.a), .b(dif.b));

    initial begin
        environment = new("env");
        uvm_resource_db#(virtual inverter_if)::set("env",
            "inverter_if", dif);
        run_test();
    end
endmodule
