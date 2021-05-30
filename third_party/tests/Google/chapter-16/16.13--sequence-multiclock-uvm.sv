// Copyright (C) 2019-2021  The SymbiFlow Authors.
//
// Use of this source code is governed by a ISC-style
// license that can be found in the LICENSE file or at
// https://opensource.org/licenses/ISC
//
// SPDX-License-Identifier: ISC


/*
:name: sequence_multiclock_test_uvm
:description: sequence with local variables in UVM
:type: simulation parsing
:tags: uvm uvm-assertions
:timeout: 60
*/

import uvm_pkg::*;
`include "uvm_macros.svh"

module clk_gen(
    input      clk0,
    input      clk1,
    output reg out0,
    output reg out1
);

    initial begin
        out0 = 0;
        out1 = 0;
    end

    always @(posedge clk0) begin
        out0 <= 1;
    end

    always @(posedge clk1) begin
        out1 <= 1;
    end

endmodule: clk_gen

interface clk_gen_if(
    output bit clk0,
    output bit clk1,
    input      out0,
    input      out1
);

endinterface: clk_gen_if

string label = "SEQUENCE_MULTICLOCK_UVM";

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
            repeat(10) @(posedge m_if.clk0);
        end
        `uvm_info(label, "Finished run phase", UVM_LOW);
        phase.drop_objection(this);
    endtask: run_phase
endclass

module top();
    env environment;

    clk_gen_if dif();

    clk_gen dut(.clk0(dif.clk0), .clk1(dif.clk1), .out0(dif.out0), .out1(dif.out1));

    initial begin
        environment = new("env");
        uvm_resource_db#(virtual clk_gen_if)::set("env",
            "clk_gen_if", dif);
        dif.clk0 = 0;
        dif.clk1 = 0;
        run_test();
    end

    sequence seq;
        @(posedge dif.clk0) ##1 dif.out0 ##1 @(posedge dif.clk1) dif.out1;
    endsequence

    assert property (seq) else `uvm_error(label, $sformatf("sequence check failed :assert: (False)"));

    initial begin
        forever begin
            #(50) dif.clk0 = ~dif.clk0;
            #(150) dif.clk1 = ~dif.clk1;
        end
    end
endmodule
