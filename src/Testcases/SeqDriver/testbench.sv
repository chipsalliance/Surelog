//
// This example illustrates how to implement a unidirectional sequence-driver
// use model. The example used is an ADPCM like undirectional comms protocol.
// There is no response, so there is no DUT, just an interface ---->
//
// "Open EPWave after run" to see the signal traffic being sent.
//

// To resolve unknown package: `include "uvm_pkg.sv"
package adpcm_pkg;

import uvm_pkg::*;
`include "uvm_macros.svh"

// Sequence item contains the data and a delay before
// sending the data frame
//
class adpcm_seq_item extends uvm_sequence_item;

rand logic[31:0] data;
rand int delay;

constraint c_delay { delay > 0; delay <= 20; }
  
`uvm_object_utils(adpcm_seq_item)

function new(string name = "adpcm_seq_item");
  super.new(name);
endfunction

function void do_copy(uvm_object rhs);
  adpcm_seq_item rhs_;

  if(!$cast(rhs_, rhs)) begin
    uvm_report_error("do_copy", "cast failed, check types");
  end
  data = rhs_.data;
  delay = rhs_.delay;
endfunction: do_copy

function bit do_compare(uvm_object rhs, uvm_comparer comparer);
  adpcm_seq_item rhs_;

  do_compare = $cast(rhs_, rhs) &&
               super.do_compare(rhs, comparer) &&
               data == rhs_.data &&
               delay == rhs_.delay;
endfunction: do_compare

function string convert2string();
  return $sformatf(" data:\t%0h\n delay:\t%0d", data, delay);
endfunction: convert2string

function void do_print(uvm_printer printer);

  if(printer.knobs.sprint == 0) begin
    $display(convert2string());
  end
  else begin
    printer.m_string = convert2string();
  end

endfunction: do_print

function void do_record(uvm_recorder recorder);
  super.do_record(recorder);

  `uvm_record_field("data", data);
  `uvm_record_field("delay", delay);

endfunction: do_record

endclass: adpcm_seq_item

// Unidirectional driver uses the get_next_item(), item_done() approach
//
class adpcm_driver extends uvm_driver #(adpcm_seq_item);

`uvm_component_utils(adpcm_driver)

adpcm_seq_item req;

virtual adpcm_if.mon_mp ADPCM;

function new(string name = "adpcm_driver", uvm_component parent = null);
  super.new(name, parent);
endfunction

task run_phase(uvm_phase phase);
  int top_idx = 0;

  // Default conditions:
  ADPCM.cb.frame <= 0;
  ADPCM.cb.data <= 0;
  fork
  forever
    begin
      seq_item_port.get_next_item(req); // Gets the sequence_item from the sequence
      repeat(req.delay) begin // Delay between packets
        @(ADPCM.cb);
      end
      ADPCM.cb.frame <= 1; // Start of frame
      for(int i = 0; i < 8; i++) begin // Send nibbles
        @(ADPCM.cb);
        ADPCM.cb.data <= req.data[3:0];
        req.data = req.data >> 4;
      end
      ADPCM.cb.frame <= 0; // End of frame
      seq_item_port.item_done(); // Indicates that the sequence_item has been consumed
    end
  forever begin
    @(ADPCM.cb);
    if (ADPCM.cb.frame === 1'b1) begin
      $display($time);
    end
  end
  join_none
endtask: run_phase

endclass: adpcm_driver

class adpcm_sequencer extends uvm_sequencer #(adpcm_seq_item);

`uvm_component_utils(adpcm_sequencer)

function new(string name = "adpcm_sequencer", uvm_component parent = null);
  super.new(name, parent);
endfunction

endclass: adpcm_sequencer

// Sequence part of the use model
//
// The sequence randomizes 10 ADPCM data packets and sends
// them
//
class adpcm_tx_seq extends uvm_sequence #(adpcm_seq_item);

`uvm_object_utils(adpcm_tx_seq)

// ADPCM sequence_item
adpcm_seq_item req;

// Controls the number of request sequence items sent
rand int no_reqs = 10;

function new(string name = "adpcm_tx_seq");
  super.new(name);
  // do_not_randomize = 1'b1; // Required for ModelSim
endfunction

task body;
  req = adpcm_seq_item::type_id::create("req");

  for(int i = 0; i < no_reqs; i++) begin
    start_item(req);
    // req.randomize();
    // For ModelSim, use $urandom to achieve randomization for your request
    req.delay = $urandom_range(1, 20);
    req.data = $urandom();
    finish_item(req);
    `uvm_info("ADPCM_TX_SEQ_BODY", $sformatf("Transmitted frame %0d", i), UVM_LOW)
  end
endtask: body

endclass: adpcm_tx_seq


// Test instantiates, builds and connects the driver and the sequencer
// then runs the sequence
//
class adpcm_test extends uvm_test;

`uvm_component_utils(adpcm_test)

adpcm_tx_seq test_seq;
adpcm_driver m_driver;
adpcm_sequencer m_sequencer;

function new(string name = "adpcm_test", uvm_component parent = null);
  super.new(name, parent);
endfunction

function void build_phase(uvm_phase phase);
  m_driver = adpcm_driver::type_id::create("m_driver", this);
  m_sequencer = adpcm_sequencer::type_id::create("m_sequencer", this);
endfunction: build_phase

function void connect_phase(uvm_phase phase);
  m_driver.seq_item_port.connect(m_sequencer.seq_item_export);
  if (!uvm_config_db #(virtual adpcm_if.mon_mp)::get(this, "",
    "ADPCM_vif", m_driver.ADPCM)) begin
    `uvm_error("connect", "ADPCM_vif not found")
  end
endfunction: connect_phase

task run_phase(uvm_phase phase);
  test_seq = adpcm_tx_seq::type_id::create("test_seq");

  phase.raise_objection(this, "starting test_seq");
  test_seq.start(m_sequencer);
  phase.drop_objection(this, "finished test_seq");
endtask: run_phase

endclass: adpcm_test

endpackage: adpcm_pkg


module top_tb;

import uvm_pkg::*;
import adpcm_pkg::*;

adpcm_if ADPCM();

// Free running clock
initial
  begin
    ADPCM.clk = 0;
    forever begin
      #10 ADPCM.clk = ~ADPCM.clk;
    end
  end

// UVM start up:
initial
  begin
    uvm_config_db #(virtual adpcm_if.mon_mp)::set(null, "uvm_test_top", "ADPCM_vif" , ADPCM);
    run_test("adpcm_test");
  end
  
// Dump waves
  initial $dumpvars(0, top_tb);

endmodule: top_tb

// This file has been modified from the original.
// Attribution and license:
//----------------------------------------------------------
//   Copyright 2010 Mentor Graphics Corporation
//   All Rights Reserved Worldwide
//
//   Licensed under the Apache License, Version 2.0 (the
//   "License"); you may not use this file except in
//   compliance with the License.  You may obtain a copy of
//   the License at
//
//       http://www.apache.org/licenses/LICENSE-2.0
//
//   Unless required by applicable law or agreed to in
//   writing, software distributed under the License is
//   distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR
//   CONDITIONS OF ANY KIND, either express or implied.  See
//   the License for the specific language governing
//   permissions and limitations under the License.
//----------------------------------------------------------