// $Id: xbus_demo_tb.sv,v 1.2 2008/08/22 16:09:36 jlrose Exp $
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

`ifndef XBUS_DEMO_TB_SV
`define XBUS_DEMO_TB_SV

`include "xbus_demo_scoreboard.sv"
`include "xbus_master_seq_lib.sv"
`include "xbus_example_master_seq_lib.sv"
`include "xbus_slave_seq_lib.sv"

// JMF small cleanup when end_of_elab is bottom-up

//------------------------------------------------------------------------------
//
// CLASS: xbus_demo_tb
//
//------------------------------------------------------------------------------

class xbus_demo_tb extends ovm_env;

  // Provide implementations of virtual methods such as get_type_name and create
  `ovm_component_utils(xbus_demo_tb)

  // xbus environment
  xbus_env xbus0;

  // Scoreboard to check the memory operation of the slave.
  xbus_demo_scoreboard scoreboard0;

  // new
  function new (string name, ovm_component parent=null);
    super.new(name, parent);
  endfunction : new

  // build
  virtual function void build();
    super.build();
    set_config_int("xbus0", "num_masters", 1);
    set_config_int("xbus0", "num_slaves", 1);
    xbus0 = xbus_env::type_id::create("xbus0", this);
    scoreboard0 = xbus_demo_scoreboard::type_id::create("scoreboard0", this);
  endfunction : build

  function void connect();
    // Connect slave0 monitor to scoreboard
    xbus0.slaves[0].monitor.item_collected_port.connect(
      scoreboard0.item_collected_export);
    // Assign interface for xbus0
    xbus0.assign_vi(xbus_tb_top.xi0);
  endfunction : connect

  function void end_of_elaboration();
    // Set up slave address map for xbus0 (basic default)
    xbus0.set_slave_address_map("slaves[0]", 0, 16'hffff);
  endfunction : end_of_elaboration

endclass : xbus_demo_tb

`endif // XBUS_DEMO_TB_SV

