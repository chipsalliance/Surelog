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


`define VMM_HW_ARCH_NULL

`include "vmm.sv"
`include "vmm_ral.sv"
`include "vmm_sb.sv"
`include "vmm_hw.sv"
`include "vmm_perf.sv"

program test;

initial
begin
   begin
      vmm_version v = new;
      v.display();
   end
   begin
      vmm_ral_version v = new;
      v.display();
   end
   begin
      vmm_sb_version v = new;
      v.display();
   end
   begin
      vmm_hw_version v = new;
      v.display();
   end
   begin
      vmm_perf_version v = new;
      v.display();
   end
end

endprogram
