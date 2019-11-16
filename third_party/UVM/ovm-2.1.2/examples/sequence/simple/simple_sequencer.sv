// $Id: simple_sequencer.sv,v 1.4 2008/08/22 16:09:36 jlrose Exp $
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

`ifndef SIMPLE_SEQUENCER_SV
`define SIMPLE_SEQUENCER_SV


//------------------------------------------------------------------------------
//
// CLASS: simple_sequencer
//
// declaration
//------------------------------------------------------------------------------

class simple_sequencer extends ovm_sequencer #(simple_item);

  // Constructor
  function new (string name, ovm_component parent);
    super.new(name, parent);
    `ovm_update_sequence_lib_and_item(simple_item)
  endfunction : new

  // Provide implementations of virtual methods such as get_type_name and create
  `ovm_sequencer_utils(simple_sequencer)

endclass : simple_sequencer


`endif // SIMPLE_SEQUENCER_SV
