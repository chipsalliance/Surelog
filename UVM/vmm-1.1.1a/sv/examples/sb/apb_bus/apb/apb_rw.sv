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


`ifndef APB_RW__SV
`define APB_RW__SV

`include "vmm.sv"

class apb_rw extends vmm_data;
   static vmm_log log = new("apb_rw", "class");

   rand enum {READ, WRITE} kind;
   rand bit   [31:0] addr;
   rand logic [31:0] data;

   function new();
      super.new(this.log);
   endfunction: new

   virtual function vmm_data allocate();
      apb_rw tr = new;
      return tr;
   endfunction: allocate

   virtual function vmm_data copy(vmm_data to = null);
      apb_rw tr;

      if (to == null) tr = new;
      else if (!$cast(tr, to)) begin
         `vmm_fatal(log, "Cannot copy into non-apb_rw instance");
         return null;
      end

      super.copy_data(tr);
      tr.kind = this.kind;
      tr.addr = this.addr;
      tr.data = this.data;

      return tr;
   endfunction: copy

   virtual function string psdisplay(string prefix = "");
      $sformat(psdisplay, "%sAPB %s @ 0x%h = 0x%h", prefix,
               this.kind.name(), this.addr, this.data);
   endfunction: psdisplay

   virtual function bit is_valid(bit silent = 1,
                                 int kind   = -1);
      return 1;
   endfunction: is_valid

   virtual function bit compare(input  vmm_data to,
                                output string   diff,
                                input  int      kind = -1);
      apb_rw tr;

      if (to == null) begin
         `vmm_fatal(log, "Cannot compare to NULL reference");
         return 0;
      end
      else if (!$cast(tr, to)) begin
         `vmm_fatal(log, "Cannot compare against non-apb_rw instance");
         return 0;
      end

      if (this.kind != tr.kind) begin
         $sformat(diff, "Kind %s !== %s", this.kind, tr.kind);
         return 0;
      end

      if (this.addr !== tr.addr) begin
         $sformat(diff, "Addr 0x%h !== 0x%h", this.addr, tr.addr);
         return 0;
      end

      if (this.data !== tr.data) begin
         $sformat(diff, "Data 0x%h !== 0x%h", this.data, tr.data);
         return 0;
      end

      return 1;
   endfunction: compare

endclass: apb_rw

`vmm_channel(apb_rw)
`vmm_atomic_gen(apb_rw, "APB Bus Cycle")
`vmm_scenario_gen(apb_rw, "APB Bus Cycle")

`endif
