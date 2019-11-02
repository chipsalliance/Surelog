// $Id: //dvt/vtech/dev/main/ovm-tests/examples/hello_world/ovm/hello_world.sv#1 $
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
`timescale 1ns / 1ns

module hello_world;

  `include "ovm.svh"

  `include "packet.sv"
  `include "producer.sv"
  `include "consumer.sv"
  `include "top.sv"
 
  top mytop;

  initial begin
    $timeformat(-9,0," ns",5);
    ovm_default_table_printer.knobs.name_width=20;
    ovm_default_table_printer.knobs.type_width=50;
    ovm_default_table_printer.knobs.size_width=10;
    ovm_default_table_printer.knobs.value_width=14;
    set_config_int("top.producer1","num_packets",2);
    set_config_int("top.producer2","num_packets",4);
    set_config_int("*","recording_detail",OVM_LOW);
    ovm_top.enable_print_topology = 1;
    //ovm_default_printer = ovm_default_tree_printer;
    ovm_default_printer.knobs.reference=0;
    mytop = new("top"); 
    ovm_default_table_printer.knobs.type_width=20;
    run_test();
  end

  initial #1us ovm_top.stop_request(); // stops run phase @ 1us

endmodule

