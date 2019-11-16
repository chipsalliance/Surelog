//----------------------------------------------------------------------
//   Copyright 2007-2008 Mentor Graphics Corporation
//   Copyright 2007-2008 Cadence Design Systems, Inc.
//   All Rights Reserved Worldwide
//
//   Ported to VMM, 2008 by Synopsys, Inc.
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


class simple_driver extends vmm_xactor;

  simple_item_channel in_chan;

  // Constructor
  function new (string name, simple_item_channel in_chan = null);
    super.new("Simple Driver", name);
    if (in_chan == null) in_chan = new("Simple Driver Input Channel",
                                       {name, ".in_chan"});
    this.in_chan = in_chan;
  endfunction : new

  task main ();
    while(1) begin
      simple_item item;
      #10;
      this.in_chan.activate(item);
      `vmm_note(this.log, "Printing received item :");
      item.display();
      void'(this.in_chan.remove());
    end
  endtask: main

endclass : simple_driver


`endif // SIMPLE_DRIVER_SV
