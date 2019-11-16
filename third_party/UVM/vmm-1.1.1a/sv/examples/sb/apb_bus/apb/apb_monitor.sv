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


`ifndef APB_MONITOR__SV
`define APB_MONITOR__SV

`include "apb_if.sv"
`include "apb_rw.sv"


typedef class apb_monitor;
class apb_monitor_cbs extends vmm_xactor_callbacks;
   virtual function void post_cycle(apb_monitor xactor,
                                    apb_rw     cycle);
   endfunction: post_cycle
endclass: apb_monitor_cbs


class apb_monitor extends vmm_xactor;
   virtual apb_if.passive sigs;
   apb_rw_channel         out_chan;

   typedef enum {OBSERVED} notifications_e;

   apb_rw tr_factory;

   function new(string                 name,
                int unsigned           stream_id,
                virtual apb_if.passive sigs,
                apb_rw_channel         out_chan   = null,
                apb_rw                 tr_factory = null);
      super.new("APB Monitor", name, stream_id);
      this.sigs = sigs;

      if (out_chan == null) begin
         out_chan = new("APB Monitor Output Channel", name);
         out_chan.sink();
      end
      this.out_chan = out_chan;

      if (tr_factory == null) tr_factory = new;
      this.tr_factory = tr_factory;

      void'(this.notify.configure(OBSERVED));
   endfunction: new


   virtual function void reset_xactor(reset_e rst_typ = SOFT_RST);
      super.reset_xactor(rst_typ);
      this.out_chan.flush();
   endfunction: reset_xactor


   virtual protected task main();
      super.main();
      forever begin
         apb_rw tr;
         bit drop;

         this.wait_if_stopped();

         `vmm_trace(log, "Waiting for start of transaction...");

         // Wait for a SETUP cycle
         do begin
            @ (this.sigs.pck);
         end
         while (this.sigs.pck.psel !== 1'b1 ||
                this.sigs.pck.penable !== 1'b0);

         $cast(tr, this.tr_factory.allocate());
         tr.notify.indicate(vmm_data::STARTED);

         tr.kind = (this.sigs.pck.pwrite) ? apb_rw::WRITE : apb_rw::READ;
         tr.addr = this.sigs.pck.paddr;

         @ (this.sigs.pck);
         if (this.sigs.pck.penable !== 1'b1) begin
            `vmm_error(this.log, "APB protocol violation: SETUP cycle not followed by ENABLE cycle");
         end
         tr.data = (tr.kind == apb_rw::READ) ? this.sigs.pck.prdata :
                                               this.sigs.pck.pwdata;
         tr.notify.indicate(vmm_data::ENDED);

         `vmm_callback(apb_monitor_cbs, post_cycle(this, tr));

         `vmm_trace(log, {"Observed transaction...\n",
                          tr.psdisplay("   ")});

         this.notify.indicate(OBSERVED, tr);
         this.out_chan.sneak(tr);
      end
   endtask: main

endclass: apb_monitor

`endif
