
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

/*
About: 'ep' event poll
This test is a simple test that will cover the creation of two ovm_events using the ovm_event_pool. Then use the ovm_event_pool methods to print those objects.


For a full documentation of the ovm_event and ovm_event_pool, check the files:
	- ovm/src/base/ovm_event.svh
	- ovm/src/base/ovm_event.sv
*/



module test;
  import ovm_pkg::*;

  ovm_event_pool ep=new("ep");

  initial begin
    ovm_event e;
    e = ep.get("fred");
    e = ep.get("george");
    ovm_default_table_printer.knobs.reference = 0;
    ep.print();
  end
endmodule
