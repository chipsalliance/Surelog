// 
// -------------------------------------------------------------
//    Copyright 2004-2008 Synopsys, Inc.
//    Copyright 2009 Mentor Graphics Corporation
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


`ifndef VMM_PERF_TENURE__SV
`define VMM_PERF_TENURE__SV

`include "vmm.sv"

class vmm_perf_tenure;

   local static int unsigned next_tenure_id = 0;

   local int unsigned tenure_id;
   local int unsigned initiator_id;
   local int unsigned target_id;

   local vmm_data tr;

   extern function new(int unsigned initiator_id = 0,
                       int unsigned target_id    = 0,
                       vmm_data     tr           = null);

   extern function int unsigned get_tenure_id();
   extern function int unsigned get_initiator_id();
   extern function int unsigned get_target_id();
   extern function vmm_data     get_tr();

   extern virtual function string psdisplay(string prefix = "");
endclass: vmm_perf_tenure


function vmm_perf_tenure::new(int unsigned initiator_id = 0,
                              int unsigned target_id = 0,
                              vmm_data     tr = null);
   this.tenure_id    = this.next_tenure_id++;
   this.initiator_id = initiator_id;
   this.target_id    = target_id;
   this.tr           = tr;
endfunction: new


function int unsigned vmm_perf_tenure::get_tenure_id();
   return this.tenure_id;
endfunction: get_tenure_id

function int unsigned vmm_perf_tenure::get_initiator_id();
   return this.initiator_id;
endfunction: get_initiator_id


function int unsigned vmm_perf_tenure::get_target_id();
   return this.target_id;
endfunction: get_target_id


function vmm_data vmm_perf_tenure::get_tr();
   return this.tr;
endfunction: get_tr


function string vmm_perf_tenure::psdisplay(string prefix = "");
   $sformat(psdisplay, "%sTenure #%0d, %0d->%0d", prefix,
            this.tenure_id, this.initiator_id, this.target_id);
   if (this.tr != null) begin
      $sformat(psdisplay, "%s\n%s", psdisplay, this.tr.psdisplay({prefix, "   "}));
   end
endfunction: psdisplay


`endif // VMM_PERF_TENURE__SV
