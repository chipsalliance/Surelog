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


virtual class vmm_ral_reg_backdoor;
   static vmm_log log = new("vmm_ral_reg_backdoor", "class");
   
   extern virtual task write(output vmm_rw::status_e              status,
                             input  bit [`VMM_RAL_DATA_WIDTH-1:0] data,
                             input  int                           data_id,
                             input  int                           scenario_id,
                             input  int                           stream_id);
   extern virtual task read(output vmm_rw::status_e              status,
                            output bit [`VMM_RAL_DATA_WIDTH-1:0] data,
                            input  int                           data_id,
                            input  int                           scenario_id,
                            input  int                           stream_id);
endclass: vmm_ral_reg_backdoor


virtual class vmm_ral_mem_backdoor;
   static vmm_log log = new("vmm_ral_mem_backdoor", "class");
   
   extern virtual task write(output vmm_rw::status_e              status,
                             input  bit [`VMM_RAL_ADDR_WIDTH-1:0] offset,
                             input  bit [`VMM_RAL_DATA_WIDTH-1:0] data,
                             input  int                           data_id,
                             input  int                           scenario_id,
                             input  int                           stream_id);
   extern virtual task read(output vmm_rw::status_e              status,
                            input  bit [`VMM_RAL_ADDR_WIDTH-1:0] offset,
                            output bit [`VMM_RAL_DATA_WIDTH-1:0] data,
                            input  int                           data_id,
                            input  int                           scenario_id,
                            input  int                           stream_id);
endclass: vmm_ral_mem_backdoor


task vmm_ral_reg_backdoor::write(output vmm_rw::status_e              status,
                                 input  bit [`VMM_RAL_DATA_WIDTH-1:0] data,
                                 input  int                           data_id,
                                 input  int                           scenario_id,
                                 input  int                           stream_id);
   `vmm_fatal(this.log, "vmm_ral_reg_backdoor::write() method has not been overloaded");
endtask: write


task vmm_ral_reg_backdoor::read(output vmm_rw::status_e              status,
                                output bit [`VMM_RAL_DATA_WIDTH-1:0] data,
                                input  int                           data_id,
                                input  int                           scenario_id,
                                input  int                           stream_id);
   `vmm_fatal(this.log, "vmm_ral_reg_backdoor::read() method has not been overloaded");
endtask: read


task vmm_ral_mem_backdoor::write(output vmm_rw::status_e              status,
                                 input  bit [`VMM_RAL_ADDR_WIDTH-1:0] offset,
                                 input  bit [`VMM_RAL_DATA_WIDTH-1:0] data,
                                 input  int                           data_id,
                                 input  int                           scenario_id,
                                 input  int                           stream_id);
   `vmm_fatal(this.log, "vmm_ral_mem_backdoor::write() method has not been overloaded");
endtask: write


task vmm_ral_mem_backdoor::read(output vmm_rw::status_e              status,
                                input  bit [`VMM_RAL_ADDR_WIDTH-1:0] offset,
                                output bit [`VMM_RAL_DATA_WIDTH-1:0] data,
                                input  int                           data_id,
                                input  int                           scenario_id,
                                input  int                           stream_id);
   `vmm_fatal(this.log, "vmm_ral_mem_backdoor::read() method has not been overloaded");
endtask: read
