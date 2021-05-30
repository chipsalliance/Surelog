// Copyright (C) 2019-2021  The SymbiFlow Authors.
//
// Use of this source code is governed by a ISC-style
// license that can be found in the LICENSE file or at
// https://opensource.org/licenses/ISC
//
// SPDX-License-Identifier: ISC


/*
:name: property_local_var_test_uvm
:description: property with local variables in UVM
:type: simulation parsing
:tags: uvm uvm-assertions
:timeout: 60
*/

import uvm_pkg::*;
`include "uvm_macros.svh"

module clk_gen(
    input            valid,
    input            clk,
    output reg [7:0] out,
    input      [7:0] in
);

    reg [7:0] data_reg_0;
    reg [7:0] data_reg_1;
    reg [7:0] data_reg_2;

    initial begin
        data_reg_0 = 0;
        data_reg_1 = 0;
        data_reg_2 = 0;
        out        = 0;
    end

    always @(posedge clk) begin
        if (valid) begin
            data_reg_0 <= in + 1;
            data_reg_1 <= data_reg_0 + 1;
            data_reg_2 <= data_reg_1 + 1;
            out        <= data_reg_2 + 1;
        end
    end

endmodule: clk_gen

interface clk_gen_if(
    output bit       valid,
    output bit       clk,
    input      [7:0] out,
    output bit [7:0] in
);

endinterface: clk_gen_if

string label = "SEQUENCE_LOCAL_VAR_UVM";

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

    clk_gen dut(.valid(dif.valid), .clk(dif.clk), .out(dif.out), .in(dif.in));

    initial begin
        environment = new("env");
        uvm_resource_db#(virtual clk_gen_if)::set("env",
            "clk_gen_if", dif);
        dif.clk   = 0;
        dif.valid = 1;
        run_test();
    end

    property prop;
        int x;
        @(posedge dif.clk) (dif.valid, x = dif.in) |-> ##4 (dif.out == x + 4);
    endproperty

    assert property (prop) else `uvm_info(label, $sformatf("property check failed :assert: (False)"), UVM_LOW);

    assign dif.in = cycle;

    always @(posedge dif.clk)
        cycle = cycle + 1;

    initial begin
        forever begin
            #(50) dif.clk = ~dif.clk;
        end
    end
endmodule
