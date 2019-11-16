//----------------------------------------------------------------------
//   Copyright 2007-2010 Mentor Graphics Corporation
//   Copyright 2007-2010 Cadence Design Systems, Inc.
//   Copyright 2010-2011 Synopsys, Inc.
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


module top;
  import uvm_pkg::*;
  import my_env_pkg::*;

  my_env topenv;

  initial begin
    uvm_default_printer = uvm_default_table_printer;
    uvm_top.enable_print_topology = 1;

    //set configuration prior to creating the environment
    set_config_int("topenv.*.u1", "v", 30);
    set_config_int("topenv.inst2.u1", "v", 10);
    set_config_int("topenv.*", "debug", 1);
    set_config_string("*", "myaa[foo]", "hi");
    set_config_string("*", "myaa[bar]", "bye");
    set_config_string("*", "myaa[foobar]", "howdy");
    set_config_string("topenv.inst1.u1", "myaa[foo]", "boo");
    set_config_string("topenv.inst1.u1", "myaa[foobar]", "boobah");

    topenv = new("topenv", null);
    run_test();

  end

endmodule
