//
// -------------------------------------------------------------
//    Copyright 2004-2008 Synopsys, Inc.
//    All Rights Reserved Worldwide
//
//    Licensed under the Apache License, Version 2.0 (the
//    "License"); you may not use this file except in
//    compliance with the License.  You may obtain a copy of
//    the License at
//
//        http://www.apache.org/licenses/LICENSE-2.0
//
//    Unless required by applicable law or agreed to in
//    writing, software distributed under the License is
//    distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR
//    CONDITIONS OF ANY KIND, either express or implied.  See
//    the License for the specific language governing
//    permissions and limitations under the License.
// -------------------------------------------------------------
//


class trans extends vmm_data;
  typedef enum bit {READ=1'b0, WRITE=1'b1} kind_e;

  rand bit [31:0] addr;
  rand bit [31:0] data;
  rand kind_e     kind;

  `vmm_data_member_begin(trans)
     `vmm_data_member_scalar(addr, DO_ALL)
     `vmm_data_member_scalar(data, DO_ALL)
     `vmm_data_member_enum(kind, DO_ALL)
  `vmm_data_member_end(trans)
endclass
`vmm_channel(trans)
`vmm_atomic_gen(trans, "Gen")
