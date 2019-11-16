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


class alu_data extends vmm_data;
   typedef enum bit [2:0] {ADD=3'b000, SUB=3'b001, MUL=3'b010,
                           LS=3'b011, RS=3'b100} kind_t;
   rand kind_t kind;
   rand bit [3:0] a, b;
   rand bit [6:0] y;

   `vmm_data_member_begin(alu_data)
      `vmm_data_member_enum(kind, DO_ALL)
      `vmm_data_member_scalar(a, DO_ALL)
      `vmm_data_member_scalar(b, DO_ALL)
      `vmm_data_member_scalar(y, DO_ALL)
   `vmm_data_member_end(alu_data)
endclass

`vmm_channel(alu_data)
`vmm_atomic_gen(alu_data, "ALU Data")
