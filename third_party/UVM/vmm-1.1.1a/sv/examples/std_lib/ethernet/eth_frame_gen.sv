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


//
// This generator is identical to the one produced by
// the `vmm_atomic_gen() macro.
//

typedef class eth_frame_gen;
class eth_frame_gen_callbacks extends vmm_xactor_callbacks;
   virtual task post_inst_gen(eth_frame_gen gen,
                              eth_frame     fr,
                              ref bit       drop);
   endtask
endclass


// Example 4-14
// Example 5-1
class eth_frame_gen extends vmm_xactor;

   integer unsigned stop_after_n_insts;

   typedef enum integer {GENERATED, DONE} symbols_e;

   // Example 5-7
   // Example 5-27
   eth_frame randomized_fr;

   // Example 5-2
   eth_frame_channel out_chan;

   local integer scenario_count;
   local integer fr_count;

   // Example 5-3
   function new(string            inst,
                integer           stream_id = -1,
                eth_frame_channel out_chan  = null);
      super.new("Ethernet Frame Generator", inst, stream_id);

      if (out_chan == null) begin
         out_chan = new("Ethernet Frame Generator output channel",
                         inst);
      end
      this.out_chan = out_chan;
      this.log.is_above(this.out_chan.log);

      this.scenario_count = 0;
      this.fr_count = 0;
      this.stop_after_n_insts = 0;

      void'(this.notify.configure(GENERATED, vmm_notify::ONE_SHOT));
      void'(this.notify.configure(DONE, vmm_notify::ON_OFF));

      // Example 5-7
      this.randomized_fr = new;
   endfunction: new

   // Example 5-12
   virtual task inject(eth_frame fr,
                       ref bit   dropped);
      dropped = 0;

      `vmm_callback(eth_frame_gen_callbacks,
                    post_inst_gen(this, fr, dropped));

      if (!dropped) begin
         this.fr_count++;
         this.notify.indicate(GENERATED, fr);
         this.out_chan.put(fr);
      end
   endtask: inject

   virtual function void reset_xactor(reset_e rst_typ = SOFT_RST);
      super.reset_xactor(rst_typ);

      this.out_chan.flush();
      this.scenario_count = 0;
      this.fr_count = 0;

      if (rst_typ >= FIRM_RST) begin
         this.notify.reset( , vmm_notify::HARD);
      end

      if (rst_typ >= HARD_RST) begin
         this.stop_after_n_insts = 0;
         this.randomized_fr     = new;
      end
   endfunction: reset_xactor

   virtual protected task main();
      bit dropped;

      fork
         super.main();
      join_none

      this.fr_count = 0;
      while (this.stop_after_n_insts <= 0 ||
             this.fr_count < this.stop_after_n_insts) begin

         this.wait_if_stopped();

         // Example 5-9
         this.randomized_fr.stream_id   = this.stream_id;
         this.randomized_fr.scenario_id = this.scenario_count;
         this.randomized_fr.data_id     = this.fr_count;

         // Example 5-7
         // Example 5-8
         // Example 5-27
         if (!this.randomized_fr.randomize()) begin
            `vmm_error(this.log, "Unable to find a solution");
            continue;
         end

         begin
            eth_frame fr;

            $cast(fr, this.randomized_fr.copy());
            this.inject(fr, dropped);
         end
      end

      this.notify.indicate(DONE);
      this.notify.indicate(vmm_xactor::XACTOR_STOPPED);
      this.notify.indicate(vmm_xactor::XACTOR_IDLE);
      this.notify.reset(vmm_xactor::XACTOR_BUSY);
      this.scenario_count++;
   endtask: main

endclass
