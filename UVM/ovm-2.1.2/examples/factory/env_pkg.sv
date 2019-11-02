// $Id: //dvt/vtech/dev/main/ovm-tests/examples/factory/env_pkg.sv#1 $
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
package env_pkg;
  import ovm_pkg::*;
  import packet_pkg::*;
  import gen_pkg::*;

  `include "ovm_macros.svh"
  
  class env extends ovm_env;
    gen gen1;

    //Use the macro in a class to implement factory registration along with other
    //utilities (create, get_type_name). For only factory registration, use the
    // macro `ovm_component_registry(env,"env").
    `ovm_component_utils(env)
    
    function new (string name, ovm_component parent);
      ovm_component cmp;
      super.new(name, parent);
     
      //use the factory to create the generator
      gen1 = gen::type_id::create("gen1", this);

    endfunction

    task run();
      packet p;
      ovm_default_tree_printer.knobs.separator = "";
      repeat(5) begin
        #15 p = gen1.get_packet();
        `ovm_info("PKTGEN", $psprintf("Got packet: %s", p.sprint(ovm_default_tree_printer)), OVM_NONE)
      end
    endtask
  endclass
endpackage
