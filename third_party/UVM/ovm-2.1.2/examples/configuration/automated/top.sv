// $Id: //dvt/vtech/dev/main/ovm-tests/examples/configuration/automated/top.sv#1 $
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


//Begindoc: Automated Configuration
//This test will focus on testing auto configurations using the ovm_component related config methods.
//
//
//
//To get a more details about the auto config methods of the ovm component, refer to the file:
//	- ovm/src/base/ovm_component.svh , the configuration related part.
//
//
//
//Walk through the test:
//Configuration settings are stored in each component instance. 
//
//Then a search is made to verify that those components full names match the field_name that had been set.
// 
//
//The following configuration interfaces virtual methods will be override:
//
//void set_config_int (string inst_name,string field_name,ovm_bitstream_t value)
//
//void set_config_object (string inst_name,string field_name,ovm_object value, bit clone=1)
//
//void set_config_string (string inst_name,string field_name,string value)
//


module top;
  import ovm_pkg::*;
  import my_env_pkg::*;

  my_env topenv;

  initial begin
    //set configuration prior to creating the environment
    set_config_int("topenv.*.u1", "v", 30);
    set_config_int("topenv.inst2.u1", "v", 10);
    set_config_int("topenv.*", "debug", 1);
    set_config_int("*", "recording_detail", 0);
    set_config_string("*", "myaa[foo]", "hi");
    set_config_string("*", "myaa[bar]", "bye");
    set_config_string("*", "myaa[foobar]", "howdy");
    set_config_string("topenv.inst1.u1", "myaa[foo]", "boo");
    set_config_string("topenv.inst1.u1", "myaa[foobar]", "boobah");

    topenv = new("topenv", null); topenv.build();

    ovm_top.enable_print_topology=1;
    ovm_default_printer.knobs.reference=0;

    // select different default printer
    //ovm_default_printer = ovm_default_tree_printer;

    run_test();
  end

  initial #10 ovm_top.stop_request();

endmodule
