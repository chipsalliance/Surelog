// Copyright (C) 2019-2021  The SymbiFlow Authors.
//
// Use of this source code is governed by a ISC-style
// license that can be found in the LICENSE file or at
// https://opensource.org/licenses/ISC
//
// SPDX-License-Identifier: ISC


/*
:name: sequence_past_test_uvm
:description: sequence with "past" task in UVM
:type: simulation parsing
:tags: uvm uvm-assertions
:timeout: 60
*/

import uvm_pkg::*;
`include "uvm_macros.svh"

module clk_gen(
    input   clk,
    output  out
);

    int cnt = 0;
    bit clk_reg = 0;

    assign out = clk_reg;

    initial begin
        cnt = 0;
        clk_reg = 0;
    end

    always @(posedge clk) begin
        cnt <= cnt + 1;

        if (cnt > 5) begin
            clk_reg = 1;
            cnt = 5;
        end
    end

endmodule: clk_gen

interface clk_gen_if(
    output bit clk,
    input out
);

endinterface: clk_gen_if

string label = "SEQUENCE_FUNC_UVM";

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
            repeat(10) @(posedge m_if.clk);
        end
        `uvm_info(label, "Finished run phase", UVM_LOW);
        phase.drop_objection(this);
    endtask: run_phase
endclass

module top();
    env environment;

    int cycle = 0;

    clk_gen_if dif();

    clk_gen dut(.clk(dif.clk), .out(dif.out));

    initial begin
        environment = new("env");
        uvm_resource_db#(virtual clk_gen_if)::set("env",
            "clk_gen_if", dif);
        dif.clk = 0;
        run_test();
    end

    sequence seq;
        @(posedge dif.clk) ~$past(dif.out) & dif.out;
    endsequence

    assert property (seq) else `uvm_info(label, $sformatf("$past(dif.out) failed :assert: (%d != 8)", cycle), UVM_LOW);

    always @(posedge dif.clk)
        cycle = cycle + 1;

    initial begin
        forever begin
            #(50) dif.clk = ~dif.clk;
        end
    end
endmodule
