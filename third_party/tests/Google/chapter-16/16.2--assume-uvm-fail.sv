// Copyright (C) 2019-2021  The SymbiFlow Authors.
//
// Use of this source code is governed by a ISC-style
// license that can be found in the LICENSE file or at
// https://opensource.org/licenses/ISC
//
// SPDX-License-Identifier: ISC


/*
:name: assume_test_fail_uvm
:description: failing assume test with UVM
:should_fail_because: adder returns wrong value and assume expects correct result (a+b)
:type: simulation
:tags: uvm uvm-assertions
*/

import uvm_pkg::*;
`include "uvm_macros.svh"

module adder (
    input clk,
    input [7:0] a,
    input [7:0] b,
    output reg [8:0] c
);

    always @ (posedge clk) begin
        c <= a + a;
    end

endmodule: adder

interface adder_if(
    output bit clk,
    output reg [7:0] a,
    output reg [7:0] b,
    input [8:0] c
);

endinterface: adder_if

string label = "ASSERT_UVM";

class env extends uvm_env;
    virtual adder_if m_if;

    function new(string name, uvm_component parent = null);
        super.new(name, parent);
    endfunction

    function void connect_phase(uvm_phase phase);
        `uvm_info(label, "Started connect phase", UVM_LOW);
        assert(uvm_resource_db#(virtual adder_if)::read_by_name(
            get_full_name(), "adder_if", m_if));
        `uvm_info(label, "Finished connect phase", UVM_LOW);
    endfunction: connect_phase

    task run_phase(uvm_phase phase);
        phase.raise_objection(this);
        `uvm_info(label, "Started run phase", UVM_LOW);
        begin
            int a = 8'h35, b = 8'h79;
            @(m_if.clk);
            m_if.a <= a;
            m_if.b <= b;

            repeat(3) @(m_if.clk);
                assume (m_if.c == (a + b)) else `uvm_error(label, $sformatf("c(%0d) != a + b(%0d) :assert: (False)", m_if.c, a + b));
        end
        `uvm_info(label, "Finished run phase", UVM_LOW);
        phase.drop_objection(this);
    endtask: run_phase
endclass

module top;
    env environment;

    adder_if dif();

    adder dut(.clk(dif.clk), .a(dif.a), .b(dif.b), .c(dif.c));

    initial begin
        environment = new("env");
        uvm_resource_db#(virtual adder_if)::set("env",
            "adder_if", dif);
        dif.clk = 0;
        run_test();
    end

    initial begin
        forever begin
            #(50) dif.clk = ~dif.clk;
        end
    end
endmodule
