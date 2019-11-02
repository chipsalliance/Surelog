// $Id: simple_driver.sv,v 1.6 2009/10/30 15:29:21 jlrose Exp $
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

`ifndef SIMPLE_DRIVER_SV
`define SIMPLE_DRIVER_SV


//------------------------------------------------------------------------------
//
// CLASS: simple_driver
//
// declaration
//------------------------------------------------------------------------------


class simple_driver extends ovm_driver #(simple_item);

  // Provide implementations of virtual methods such as get_type_name and create
  `ovm_component_utils(simple_driver)

  // Constructor
  function new (string name, ovm_component parent);
    super.new(name, parent);
  endfunction : new

  task run ();
    while(1) begin
      #10;
      seq_item_port.get_next_item(req);
      `ovm_info("Driver", "Printing received item :", OVM_MEDIUM)
      req.print();
      seq_item_port.item_done();
    end
  endtask: run

endclass : simple_driver


`endif // SIMPLE_DRIVER_SV
