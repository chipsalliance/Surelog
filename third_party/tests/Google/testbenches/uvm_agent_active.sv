// Copyright (C) 2019-2021  The SymbiFlow Authors.
//
// Use of this source code is governed by a ISC-style
// license that can be found in the LICENSE file or at
// https://opensource.org/licenses/ISC
//
// SPDX-License-Identifier: ISC


/*
:name: uvm_agent_active
:description: uvm active agent (agent + monitor + driver + sequencer) test
:tags: uvm uvm-agents
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

class packet_in extends uvm_sequence_item;
    logic [7:0] data;

    `uvm_object_utils_begin(packet_in)
        `uvm_field_int(data, UVM_ALL_ON|UVM_HEX)
    `uvm_object_utils_end

    function new(string name="packet_in");
        super.new(name);
    endfunction: new
endclass

class monitor extends uvm_monitor;
    `uvm_component_utils(monitor)
    virtual input_if  vif;
    packet_in packet;

    uvm_analysis_port #(packet_in) item_collected_port;

    function new(string name, uvm_component parent);
        super.new(name, parent);
        item_collected_port = new ("item_collected_port", this);
    endfunction

    virtual function void build_phase(uvm_phase phase);
        super.build_phase(phase);
        packet = packet_in::type_id::create("packet", this);
    endfunction

    virtual function void connect_phase(uvm_phase phase);
        super.connect_phase(phase);
        assert(uvm_resource_db#(virtual input_if)::read_by_name(
          "env", "input_if", vif));
    endfunction

    virtual task run_phase(uvm_phase phase);
        phase.raise_objection(this);
        fork
            collect_transactions(phase);
        join
        phase.drop_objection(this);
    endtask

    virtual task collect_transactions(uvm_phase phase);
        packet.data = vif.data;
        item_collected_port.write(packet);
    endtask
endclass

class sequence_in extends uvm_sequence #(packet_in);
    `uvm_object_utils(sequence_in)

    function new(string name="sequence_in");
        super.new(name);
    endfunction: new

    task body;
        packet_in packet;

        packet = packet_in::type_id::create("packet");
        start_item(packet);
        packet.data = `PATTERN;
        finish_item(packet);
    endtask: body
endclass

class sequencer extends uvm_sequencer #(packet_in);
    `uvm_component_utils(sequencer)

    function new (string name = "sequencer", uvm_component parent = null);
        super.new(name, parent);
    endfunction
endclass

class driver extends uvm_driver #(packet_in);
    `uvm_component_utils(driver)
    virtual input_if vif;

    function new(string name = "driver", uvm_component parent = null);
        super.new(name, parent);
    endfunction

    virtual function void build_phase(uvm_phase phase);
        super.build_phase(phase);
    endfunction

    virtual function void connect_phase(uvm_phase phase);
        assert(uvm_resource_db#(virtual input_if)::read_by_name(
          "env", "input_if", vif));
    endfunction

    virtual task run_phase(uvm_phase phase);
        phase.raise_objection(this);
        fork
            get_and_drive(phase);
        join
        phase.drop_objection(this);
    endtask

    virtual protected task get_and_drive(uvm_phase phase);
        seq_item_port.get(req);
        drive_transfer(req);
    endtask

    virtual protected task drive_transfer(packet_in packet);
        vif.data <= packet.data;
        @(posedge vif.clk);
    endtask

endclass

class agent_active extends uvm_agent;
    sequencer sqr;
    driver  drv;
    monitor mon;

    uvm_analysis_port #(packet_in) item_collected_port;
    `uvm_component_utils(agent_active)

    function new(string name = "agent_active", uvm_component parent = null);
        super.new(name, parent);
        item_collected_port = new("item_collected_port", this);
    endfunction

    virtual function void build_phase(uvm_phase phase);
        super.build_phase(phase);
        mon = monitor::type_id::create("mon", this);
        sqr = sequencer::type_id::create("sqr", this);
        drv = driver::type_id::create("drv", this);
    endfunction

    virtual function void connect_phase(uvm_phase phase);
        super.connect_phase(phase);
        mon.item_collected_port.connect(item_collected_port);
        drv.seq_item_port.connect(sqr.seq_item_export);
    endfunction
endclass

class env extends uvm_env;
    agent_active   agent;
    virtual output_if vif;
    int data;
    sequence_in seq;

    `uvm_component_utils(env)

    function new(string name, uvm_component parent = null);
        super.new(name, parent);
    endfunction

    virtual function void build_phase(uvm_phase phase);
        super.build_phase(phase);
        agent = agent_active::type_id::create("agent", this);
        seq = sequence_in::type_id::create("seq", this);
    endfunction

    virtual function void connect_phase(uvm_phase phase);
        super.connect_phase(phase);
        assert(uvm_resource_db#(virtual output_if)::read_by_name(
          get_full_name(), "output_if", vif));
    endfunction

    virtual function void end_of_elaboration_phase(uvm_phase phase);
        super.end_of_elaboration_phase(phase);
    endfunction

    task run_phase(uvm_phase phase);
        phase.raise_objection(this);
        seq.start(agent.sqr);
        repeat(3) @(posedge vif.clk);
        phase.drop_objection(this);
    endtask
  
    virtual function void report_phase(uvm_phase phase);
        super.report_phase(phase);
        data <= vif.data;
        if(data == `PATTERN) begin
            `uvm_info("RESULT", $sformatf("Match %d == %d",
               data, `PATTERN), UVM_LOW);
        end
        else begin
            `uvm_error("RESULT", $sformatf("Mismatch %d != %d",
               data, `PATTERN));
        end
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
