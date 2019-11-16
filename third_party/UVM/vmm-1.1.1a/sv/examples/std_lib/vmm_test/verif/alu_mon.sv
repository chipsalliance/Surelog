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



typedef class alu_mon;

class alu_mon_callbacks extends vmm_xactor_callbacks;
   // Called after a new transaction has been observed
   virtual task post_mon(alu_mon  mon,
                         alu_data tr,
                         ref bit  drop);
   endtask
endclass

class alu_mon extends vmm_xactor;

   // Factory instance for transaction descriptors
   alu_data allocated_tr;

   // Interface to Intel Bus HDL signals
   virtual alu_if.monprt iport;

   // Output channel of observed transactions
   alu_data_channel out_chan;

   integer n_trans = 0;

   // Constructor
   extern function new(string                 inst,
                       integer                stream_id,
                       virtual alu_if.monprt  iport,
                       alu_data_channel       out_chan = null);

   extern protected virtual task main();

   // Monitors the bus and returns whenver a new transaction
   // has been observed
   extern virtual task monitor(ref alu_data received_mt);

endclass


function alu_mon::new(string                 inst,
                      integer                stream_id,
                      virtual alu_if.monprt  iport,
                      alu_data_channel       out_chan = null);
   super.new("ALU Monitor", inst, stream_id);

   this.allocated_tr = new;

   this.iport = iport;
   if (out_chan == null)
      out_chan = new({this.log.get_name(), " Output Channel"}, inst);
   this.out_chan = out_chan;
endfunction


task alu_mon::main();
   fork
      super.main();
   join_none

   forever begin
      alu_data tr;
      bit      drop;

      super.wait_if_stopped();

      $cast(tr, this.allocated_tr.allocate());
      this.monitor(tr);

      `vmm_debug(log, tr.psdisplay("Observed: "));

      drop = 0;
      `vmm_callback(alu_mon_callbacks, post_mon(this, tr, drop));
      if (!drop) this.out_chan.sneak(tr);
   end
endtask


task alu_mon::monitor(ref alu_data received_mt);
   bit en;

   wait (iport.mon_cb.en);
   $cast (received_mt.kind, this.iport.mon_cb.sel);
   received_mt.a    = this.iport.mon_cb.a;
   received_mt.b    = this.iport.mon_cb.b;
   @(iport.mon_cb); 
   received_mt.y    = this.iport.mon_cb.y;
endtask


