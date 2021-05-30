// Copyright (C) 2019-2021  The SymbiFlow Authors.
//
// Use of this source code is governed by a ISC-style
// license that can be found in the LICENSE file or at
// https://opensource.org/licenses/ISC
//
// SPDX-License-Identifier: ISC


/*
:name: expect_test_uvm
:description: expect in UVM
:type: simulation parsing
:tags: uvm uvm-assertions
:timeout: 60
*/

import uvm_pkg::*;
`include "uvm_macros.svh"

module mem_ctrl (
    input            clk,
    output reg       read,
    output reg       write,
    output reg [7:0] addr,
    output reg [7:0] dout,
    input      [7:0] din
);

    reg       phase;
    reg [7:0] addr_i;

    initial begin
        phase = 0;
        read = 1;
        write = 0;
    end

    always @(posedge clk) begin
        read <= 0;
        write <= 0;
        addr <= addr_i;

        if(phase) begin
            read <= 1;
        end else begin
            write <= 1;
        end

        dout <= din;
        addr_i <= addr_i + 1;
        phase <= ~phase;
    end

endmodule: mem_ctrl

interface mem_ctrl_if(
    output bit clk,
    input read,
    input write,
    input [7:0] addr,
    input [7:0] dout,
    output reg [7:0] din
);

endinterface: mem_ctrl_if

string label = "EXPECT_UVM";

class env extends uvm_env;
    virtual mem_ctrl_if m_if;

    function new(string name, uvm_component parent = null);
        super.new(name, parent);
    endfunction

    function void connect_phase(uvm_phase phase);
        `uvm_info(label, "Started connect phase", UVM_LOW);
        assert(uvm_resource_db#(virtual mem_ctrl_if)::read_by_name(
            get_full_name(), "mem_ctrl_if", m_if));
        `uvm_info(label, "Finished connect phase", UVM_LOW);
    endfunction: connect_phase

    task run_phase(uvm_phase phase);
        phase.raise_objection(this);
        `uvm_info(label, "Started run phase", UVM_LOW);
        begin
            repeat(4) @(posedge m_if.clk);
        end
        `uvm_info(label, "Finished run phase", UVM_LOW);
        phase.drop_objection(this);
    endtask: run_phase
endclass

module top();
    env environment;

    mem_ctrl_if dif();

    mem_ctrl dut(.clk(dif.clk), .read(dif.read), .write(dif.write), .addr(dif.addr), .dout(dif.dout), .din(dif.din));

    initial begin
        environment = new("env");
        uvm_resource_db#(virtual mem_ctrl_if)::set("env",
            "mem_ctrl_if", dif);
        dif.clk = 0;
        run_test();
    end

    initial begin
        expect (@(posedge dif.clk) dif.read ##1 dif.write) else `uvm_error(label, $sformatf("expect failed :assert: (False)"));
    end

    initial begin
        forever begin
            #(50) dif.clk = ~dif.clk;
        end
    end
endmodule
