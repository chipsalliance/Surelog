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


class vmm_ral_env extends `VMM_ENV;
   vmm_ral_access ral;

   extern function new(string name = "RAL-Based Verif Env");

   extern virtual task sw_reset(string domain = "");
endclass: vmm_ral_env


function vmm_ral_env::new(string name= "RAL-Based Verif Env");
   super.new(name);
   this.ral = new;
endfunction: new


task vmm_ral_env::sw_reset(string domain = "");
endtask: sw_reset
