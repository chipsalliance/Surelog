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


`ifndef VMM_SB_VERSION__SV
`define VMM_SB_VERSION__SV

class vmm_sb_version;
   function int major();
      major = 1;
   endfunction: major

   function int minor();
      minor = 4;
   endfunction: minor

   function int patch();
      patch = 3;
   endfunction: patch


   function string vendor();
      vendor = "Synopsys";
   endfunction: vendor

   function void display(string prefix = "");
      $write("%s\n", this.psdisplay(prefix));
   endfunction: display

   function string psdisplay(string prefix = "");
      $sformat(psdisplay, "%sVMM SB Package %0d.%0d.%0d (%s)",
               prefix, this.major(), this.minor(), this.patch(), this.vendor());
   endfunction: psdisplay
endclass: vmm_sb_version


`endif // VMM_SB_VERSION__SV
