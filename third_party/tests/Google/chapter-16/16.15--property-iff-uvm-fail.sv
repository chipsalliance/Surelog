// Copyright (C) 2019-2021  The SymbiFlow Authors.
//
// Use of this source code is governed by a ISC-style
// license that can be found in the LICENSE file or at
// https://opensource.org/licenses/ISC
//
// SPDX-License-Identifier: ISC


/*
:name: property_disable_iff_fail_test_uvm
:description: failing property with disable iff test with UVM
:should_fail_because: disable iff uses wrong reset polarity
:type: simulation
:tags: uvm uvm-assertions
*/

import uvm_pkg::*;
`include "uvm_macros.svh"

module clk_gen(
    input      rst,
    input      clk,
    output reg out
);

    initial begin
        out = 0;
    end

    always @(posedge clk or posedge rst) begin
        if (rst)
            out <= 0;
        else
            out <= 1;
    end

endmodule: clk_gen

interface clk_gen_if(
    output bit rst,
    output bit clk,
    input out
);

endinterface: clk_gen_if

string label = "IFF_UVM";

class env extends uvm_env;
    virtual clk_gen_if m_if;

    function new(string name, uvm_component parent = null);
        super.new(name, parent);
    endfunction

    function void connect_phase(uvm_phase phase);
        `uvm_info(label, "Started connect phase", UVM_LOW);
        assert(uvm_resource_db#(virtual clk_gen_if)::read_by_name(
            get_full_name(), "clk_gen_if", m_if));
        `uvm_info(label, "Finished connect phase", UVM_LOW);
    endfunction: connect_phase

    task run_phase(uvm_phase phase);
        phase.raise_objection(this);
        `uvm_info(label, "Started run phase", UVM_LOW);
        begin
            repeat(10) @(m_if.clk);
        end
        `uvm_info(label, "Finished run phase", UVM_LOW);
        phase.drop_objection(this);
    endtask: run_phase
endclass

module top();
    env environment;

    clk_gen_if dif();

    clk_gen dut(.clk(dif.clk), .rst(dif.rst), .out(dif.out));

    initial begin
        environment = new("env");
        uvm_resource_db#(virtual clk_gen_if)::set("env",
            "clk_gen_if", dif);
        dif.clk = 0;
        dif.rst = 1;
        run_test();
    end

    property prop;
        @(posedge dif.clk) disable iff (dif.rst) dif.out;
    endproperty

    assert property (prop) else $error($sformatf("property check failed :assert: (False)"));

    initial begin
        forever begin
            #(50) dif.clk = ~dif.clk;
        end
    end
endmodule
