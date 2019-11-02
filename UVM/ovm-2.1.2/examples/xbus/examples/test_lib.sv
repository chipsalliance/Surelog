// $Id: //dvt/vtech/dev/main/ovm-tests/examples/xbus/examples/test_lib.sv#1 $
//----------------------------------------------------------------------
//   Copyright 2007-2009 Mentor Graphics Corporation
//   Copyright 2007-2009 Cadence Design Systems, Inc.
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
//----------------------------------------------------------------------

`include "xbus_demo_tb.sv"


// Base Test
class xbus_demo_base_test extends ovm_test;

  `ovm_component_utils(xbus_demo_base_test)

  xbus_demo_tb xbus_demo_tb0;
  ovm_table_printer printer;

  function new(string name = "xbus_demo_base_test", 
    ovm_component parent=null);
    super.new(name,parent);
  endfunction : new

  virtual function void build();
    super.build();
    // Enable transaction recording for everything
    set_config_int("*", "recording_detail", OVM_FULL);
    // Create the tb
    xbus_demo_tb0 = xbus_demo_tb::type_id::create("xbus_demo_tb0", this);
    // Create a specific depth printer for printing the created topology
    printer = new();
    printer.knobs.depth = 3;
  endfunction : build

  function void end_of_elaboration();
    // Set verbosity for the bus monitor for this demo
    xbus_demo_tb0.xbus0.bus_monitor.set_report_verbosity_level(OVM_FULL);
    `ovm_info(get_type_name(),
      $psprintf("Printing the test topology :\n%s", this.sprint(printer)), OVM_LOW)
  endfunction : end_of_elaboration

  task run();
    //set a drain-time for the environment if desired
    ovm_test_done.set_drain_time(this, 50);
  endtask : run

endclass : xbus_demo_base_test


// Read Modify Write Read Test
class test_read_modify_write extends xbus_demo_base_test;

  `ovm_component_utils(test_read_modify_write)

  function new(string name = "test_read_modify_write", ovm_component parent=null);
    super.new(name,parent);
  endfunction : new

  virtual function void build();
    // Set the default sequence for the master and slave
    set_config_string("xbus_demo_tb0.xbus0.masters[0].sequencer",
      "default_sequence", "read_modify_write_seq");
    set_config_string("xbus_demo_tb0.xbus0.slaves[0].sequencer", 
      "default_sequence", "slave_memory_seq");
    // Create the tb
    super.build();
  endfunction : build

endclass : test_read_modify_write


// Large word read/write test
class test_r8_w8_r4_w4 extends xbus_demo_base_test;

  `ovm_component_utils(test_r8_w8_r4_w4)

  function new(string name = "test_r8_w8_r4_w4", ovm_component parent=null);
    super.new(name,parent);
  endfunction : new

  virtual function void build();
    // Set the default sequence for the master and slave
    set_config_string("xbus_demo_tb0.xbus0.masters[0].sequencer", 
      "default_sequence", "r8_w8_r4_w4_seq");
    set_config_string("xbus_demo_tb0.xbus0.slaves[0].sequencer", 
      "default_sequence", "slave_memory_seq");
    // Create the tb
    super.build();
  endfunction : build

endclass : test_r8_w8_r4_w4 


// 2 Master, 4 Slave test
class test_2m_4s extends xbus_demo_base_test;

  `ovm_component_utils(test_2m_4s)

  function new(string name = "test_2m_4s", ovm_component parent=null);
    super.new(name,parent);
  endfunction : new

  virtual function void build();
    // Overides to the xbus_demo_tb build()
    // Set the topology to 2 masters, 4 slaves
    set_config_int("xbus_demo_tb0.xbus0", "num_masters", 2);
    set_config_int("xbus_demo_tb0.xbus0", "num_slaves", 4);
    // Set the default sequence for the master and slave
    set_config_string("xbus_demo_tb0.xbus0.master*.sequencer", 
      "default_sequence", "loop_read_modify_write_seq");
    set_config_string("xbus_demo_tb0.xbus0.slave*.sequencer", 
      "default_sequence", "slave_memory_seq");
    // Control the number of RMW loops
    set_config_int("xbus_demo_tb0.xbus0.masters[0].sequencer",
      "loop_read_modify_write_seq.itr", 4);
    set_config_int("xbus_demo_tb0.xbus0.masters[1].sequencer",
      "loop_read_modify_write_seq.itr", 3);
    // Create the tb
    super.build();
  endfunction : build

  function void connect();
    // Connect other slaves monitor to scoreboard
    xbus_demo_tb0.xbus0.slaves[1].monitor.item_collected_port.connect(
      xbus_demo_tb0.scoreboard0.item_collected_export);
    xbus_demo_tb0.xbus0.slaves[2].monitor.item_collected_port.connect(
      xbus_demo_tb0.scoreboard0.item_collected_export);
    xbus_demo_tb0.xbus0.slaves[3].monitor.item_collected_port.connect(
      xbus_demo_tb0.scoreboard0.item_collected_export);
  endfunction : connect
  
  function void end_of_elaboration();
    // Set up slave address map for xbus0 (slaves[0] is overwritten here)
    xbus_demo_tb0.xbus0.set_slave_address_map("slaves[0]", 16'h0000, 16'h3fff);
    xbus_demo_tb0.xbus0.set_slave_address_map("slaves[1]", 16'h4000, 16'h7fff);
    xbus_demo_tb0.xbus0.set_slave_address_map("slaves[2]", 16'h8000, 16'hBfff);
    xbus_demo_tb0.xbus0.set_slave_address_map("slaves[3]", 16'hC000, 16'hFfff);
    super.end_of_elaboration();
  endfunction : end_of_elaboration

endclass : test_2m_4s
