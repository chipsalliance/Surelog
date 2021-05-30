// Copyright (C) 2019-2021  The SymbiFlow Authors.
//
// Use of this source code is governed by a ISC-style
// license that can be found in the LICENSE file or at
// https://opensource.org/licenses/ISC
//
// SPDX-License-Identifier: ISC


/*
:name: uvm_monitor_env
:description: uvm monitor + env test
:tags: uvm uvm-classes
:type: simulation parsing
:timeout: 30
*/

import uvm_pkg::*;
`include "uvm_macros.svh"

`define PATTERN 2

interface input_if(input clk);
    logic [7:0] data;
    modport port(input clk, data);
endinterface

interface output_if(input clk);
    logic [7:0] data;
    modport port(input clk, output data);
endinterface

module dut(input_if.port in, output_if.port out);
    always @(posedge in.clk)
        out.data <= in.data;
endmodule

class packet_out extends uvm_sequence_item;
    logic [7:0] data;

    `uvm_object_utils_begin(packet_out)
        `uvm_field_int(data, UVM_ALL_ON|UVM_HEX)
    `uvm_object_utils_end

    function new(string name="packet_out");
        super.new(name);
    endfunction: new
endclass

class monitor extends uvm_monitor;
    `uvm_component_utils(monitor)
    virtual output_if  vif;
    packet_out packet;

    uvm_analysis_port #(packet_out) item_collected_port;

    function new(string name, uvm_component parent);
        super.new(name, parent);
        item_collected_port = new ("item_collected_port", this);
    endfunction

    virtual function void build_phase(uvm_phase phase);
        super.build_phase(phase);
        packet = packet_out::type_id::create("packet", this);
    endfunction

    virtual function void connect_phase(uvm_phase phase);
        super.connect_phase(phase);
        assert(uvm_resource_db#(virtual output_if)::read_by_name(
          "env", "output_if", vif));
    endfunction

    virtual task run_phase(uvm_phase phase);
        super.run_phase(phase);
        fork
            collect_transactions(phase);
        join
    endtask

    virtual task collect_transactions(uvm_phase phase);
        forever begin
            repeat(2) @(posedge vif.clk);
            packet.data = vif.data;
            item_collected_port.write(packet);
            if(packet.data == `PATTERN) begin
                `uvm_info("RESULT", $sformatf("Match %d == %d",
                    packet.data, `PATTERN), UVM_LOW);
            end
            else begin
                `uvm_error("RESULT", $sformatf("Mismatch %d != %d",
                    packet.data, `PATTERN));
            end
        end
    endtask
endclass

class env extends uvm_env;
    virtual input_if vif;
    monitor mon;

    `uvm_component_utils(env)

    uvm_analysis_port #(packet_out) item_collected_port;

    function new(string name, uvm_component parent = null);
        super.new(name, parent);
        item_collected_port = new("item_collected_port", this);
    endfunction

    virtual function void build_phase(uvm_phase phase);
        super.build_phase(phase);
        mon = monitor::type_id::create("mon", this);
    endfunction

    virtual function void connect_phase(uvm_phase phase);
        super.connect_phase(phase);
        assert(uvm_resource_db#(virtual input_if)::read_by_name(
          get_full_name(), "input_if", vif));
        mon.item_collected_port.connect(item_collected_port);
    endfunction

    virtual function void end_of_elaboration_phase(uvm_phase phase);
        super.end_of_elaboration_phase(phase);
    endfunction

    task run_phase(uvm_phase phase);
        phase.raise_objection(this);
        `uvm_info("RESULT", $sformatf("Writing %0d to input interface", `PATTERN), UVM_LOW);
        vif.data <= `PATTERN;
        repeat(2) @(posedge vif.clk);
        phase.drop_objection(this);
    endtask
  
    virtual function void report_phase(uvm_phase phase);
        super.report_phase(phase);
    endfunction
endclass

module top;
    logic clk;
    env environment;

    input_if in(clk);
    output_if out(clk);
    dut d(in, out);

    always #5 clk = !clk;

    initial begin
        environment = new("env");
        uvm_resource_db#(virtual input_if)::set("env", "input_if", in);
        uvm_resource_db#(virtual output_if)::set("env",  "output_if", out);
        clk = 0;
        run_test();
    end
endmodule
