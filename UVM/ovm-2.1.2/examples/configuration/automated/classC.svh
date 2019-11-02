// $Id: //dvt/vtech/dev/main/ovm-tests/examples/configuration/automated/classC.svh#1 $
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
`ifndef CLASSC_SVH
`define CLASSC_SVH

class C extends ovm_component;
  int v=0;
  int s=0;
  string myaa[string];

  function new(string name, ovm_component parent);
    super.new(name, parent);
  endfunction

  function void build();
    super.build();
    $display("%s: In Build: v = %0d  s = %0d", get_full_name(), v, s);
  endfunction
  task run;
    begin end
  endtask

  `ovm_component_utils_begin(C)
    `ovm_field_int(v, OVM_DEFAULT)
    `ovm_field_int(s, OVM_DEFAULT)
    `ovm_field_aa_string_string(myaa, OVM_DEFAULT)
  `ovm_component_utils_end
endclass

`endif
