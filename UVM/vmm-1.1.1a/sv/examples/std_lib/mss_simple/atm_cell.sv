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

class atm_cell extends vmm_data;

  rand bit [ 3:0] gfc;
  rand bit [ 7:0] vpi;
  rand bit [15:0] vci;
  rand bit [ 2:0] pt; 
  rand bit        clp;
  rand bit [ 7:0] hec;
  rand bit [ 7:0] payload[48];
  
  constraint hec_valid {
    hec == 8'h00;   // mask field for HEC, 1s indicate bad position
  }

  constraint test;
   

  `vmm_data_member_begin(atm_cell)
     `vmm_data_member_scalar(gfc, DO_ALL)
     `vmm_data_member_scalar(vpi, DO_ALL)
     `vmm_data_member_scalar(vci, DO_ALL)
     `vmm_data_member_scalar(pt,  DO_ALL)
     `vmm_data_member_scalar(clp, DO_ALL)
     `vmm_data_member_scalar(hec, DO_ALL)
     `vmm_data_member_scalar_array(payload, DO_ALL)
  `vmm_data_member_end(atm_cell)

endclass // atm_cell

`vmm_channel(atm_cell)
`vmm_scenario_gen(atm_cell, "ATM Cell")
