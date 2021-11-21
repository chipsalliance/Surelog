//------------------------------------------------------------------------------
//  Copyright 2017 Taichi Ishitani
//
//  Licensed under the Apache License, Version 2.0 (the "License");
//  you may not use this file except in compliance with the License.
//  You may obtain a copy of the License at
//
//  http://www.apache.org/licenses/LICENSE-2.0
//
//  Unless required by applicable law or agreed to in writing, software
//  distributed under the License is distributed on an "AS IS" BASIS,
//  WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
//  See the License for the specific language governing permissions and
//  limitations under the License.
//------------------------------------------------------------------------------
`ifndef TUE_MACROS_SVH
`define TUE_MACROS_SVH

`include  "uvm_macros.svh"

`ifndef TUE_FLAT_INCLUDES
  `define tue_include_file(directory, file_name) `include `"directory/file_name`"
`else
  `define tue_include_file(directory, file_name) `include `"file_name`"
`endif

`tue_include_file(macros, tue_version_defines.svh )
`tue_include_file(macros, tue_object_defines.svh  )
`tue_include_file(macros, tue_sequence_defines.svh)

`ifdef UVM_VERSION_1_0
  `define TUE_UVM_PRE_IEEE
`elsif UVM_VERSION_1_1
  `define TUE_UVM_PRE_IEEE
`elsif UVM_VERSION_1_2
  `define TUE_UVM_PRE_IEEE
`endif

`ifdef TUE_UVM_PRE_IEEE
  `ifdef UVM_VERSION_1_0
    `define TUE_UVM_PRE_1_2
  `elsif UVM_VERSION_1_1
    `define TUE_UVM_PRE_1_2
  `endif
`endif

`endif
