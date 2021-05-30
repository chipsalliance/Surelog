// Copyright (C) 2019-2021  The SymbiFlow Authors.
//
// Use of this source code is governed by a ISC-style
// license that can be found in the LICENSE file or at
// https://opensource.org/licenses/ISC
//
// SPDX-License-Identifier: ISC


/*
:name: sequence_intersect_op_test_uvm
:description: sequence with "intersect" operator in UVM
:type: simulation parsing
:tags: uvm uvm-assertions
:timeout: 60
*/

import uvm_pkg::*;
`include "uvm_macros.svh"

module mod (
    input            clk,
    input            req,
    output reg       gnt0,
    output reg       gnt1,
    output reg       gnt2
);

    int cnt = 0;
    bit req_old = 0;

    initial begin
        gnt0 = 0;
        gnt1 = 0;
        gnt2 = 0;
    end

    always @(posedge clk) begin
        req_old <= req;
        if (req & ~req_old) begin
            cnt <= 0;
            gnt0 <= 0;
            gnt1 <= 0;
            gnt2 <= 0;
        end else begin
            if (cnt < 16) begin
                cnt <= cnt+1;
            end
            if (cnt == 3)
                gnt0 <= 1;

            if (cnt == 3)
                gnt1 <= 1;

            if (cnt == 7)
                gnt2 <= 1;
        end
    end

endmodule: mod

interface mod_if(
    output bit clk,
    output bit req,
    input gnt0,
    input gnt1,
    input gnt2
);

endinterface: mod_if

string label = "SEQUENCE_AND_UVM";

class env extends uvm_env;
    virtual mod_if m_if;

    function new(string name, uvm_component parent = null);
        super.new(name, parent);
    endfunction

    function void connect_phase(uvm_phase phase);
        `uvm_info(label, "Started connect phase", UVM_LOW);
        assert(uvm_resource_db#(virtual mod_if)::read_by_name(
            get_full_name(), "mod_if", m_if));
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

    mod_if dif();

    mod dut(.clk(dif.clk), .req(dif.req), .gnt0(dif.gnt0), .gnt1(dif.gnt1), .gnt2(dif.gnt2));

    initial begin
        environment = new("env");
        uvm_resource_db#(virtual mod_if)::set("env",
            "mod_if", dif);
        dif.clk = 0;
        run_test();
    end

    initial begin
        dif.req = 1;
    end

    sequence seq;
        @(posedge dif.clk) (dif.req ##5 dif.gnt0) intersect (dif.req ##[1:9] dif.gnt1);
    endsequence

    assert property (seq) else `uvm_error(label, $sformatf("seq failed :assert: (False)"));

    initial begin
        forever begin
            #(50) dif.clk = ~dif.clk;
        end
    end
endmodule
