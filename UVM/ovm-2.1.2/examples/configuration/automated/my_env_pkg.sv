// $Id: //dvt/vtech/dev/main/ovm-tests/examples/configuration/automated/my_env_pkg.sv#1 $
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

package my_env_pkg;
  import ovm_pkg::*;

  `include "ovm_macros.svh"
  `include "classA.svh"
  `include "classB.svh"
  
  class my_env extends ovm_env;
    bit debug = 0;
    A inst1;
    B inst2;
  
    function new(string name, ovm_component parent);
      super.new(name, parent);
    endfunction
  
    function void build();
      super.build();
      set_config_int("inst1.u2", "v", 5);
      set_config_int("inst2.u1", "v", 3);
      set_config_int("inst1.*", "s", 'h10);
  
      $display("%s: In Build: debug = %0d", get_full_name(), debug);
  
      inst1 = new("inst1", this); inst1.build();
      inst2 = new("inst2", this); inst2.build();
    endfunction

    task run;
      begin end
    endtask
  
    `ovm_component_utils_begin(my_env)
      `ovm_field_int(debug, OVM_DEFAULT)
    `ovm_component_utils_end
  endclass
  
endpackage : my_env_pkg
