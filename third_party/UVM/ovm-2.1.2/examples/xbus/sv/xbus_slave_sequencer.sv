// $Id: //dvt/vtech/dev/main/ovm-tests/examples/xbus/sv/xbus_slave_sequencer.sv#1 $
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

`ifndef XBUS_SLAVE_SEQUENCER_SV
`define XBUS_SLAVE_SEQUENCER_SV

//------------------------------------------------------------------------------
//
// CLASS: xbus_slave_sequencer
//
//------------------------------------------------------------------------------

class xbus_slave_sequencer extends ovm_sequencer #(xbus_transfer);

  // The virtual interface used to drive and view HDL signals.
  protected virtual xbus_if xsi;

  // TLM port to peek the address phase from the slave monitor
  ovm_blocking_peek_port#(xbus_transfer) addr_ph_port;

  // Provide implementations of virtual methods such as get_type_name and create
  `ovm_sequencer_utils(xbus_slave_sequencer)

  // new - constructor
  function new (string name, ovm_component parent);
    super.new(name, parent);
    `ovm_update_sequence_lib_and_item(xbus_transfer)
    addr_ph_port = new("addr_ph_port", this);
  endfunction : new

  // assign the virtual interface
  function void assign_vi(virtual interface xbus_if xsi);
    this.xsi = xsi;
  endfunction : assign_vi

endclass : xbus_slave_sequencer

`endif // XBUS_SLAVE_SEQUENCER_SV

