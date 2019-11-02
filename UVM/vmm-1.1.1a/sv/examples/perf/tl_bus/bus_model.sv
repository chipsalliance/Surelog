//
// Transaction-level model of a multi-master, multi-slave bus
//  - Atomic transactions
//  - Non pipelined
//

`ifndef BUS_MODEL__SV
`define BUS_MODEL__SV

`include "vmm.sv"
`include "bus_tr.sv"

class bus_cfg;
   rand int unsigned n_masters = 2;
   rand int unsigned n_slaves  = 2;

   constraint bus_cfg_valid {
      n_masters > 0;
      n_slaves  > 0;
   }

   constraint reasonable {
      n_masters <= 10;
      n_slaves  <= 10;
   }
endclass: bus_cfg

class bus_model extends vmm_xactor;

   bus_cfg cfg;

   bus_tr_channel master_chan[];
   bus_tr_channel slave_chan[];

   int EXECUTED;

   function new(string name, bus_cfg cfg);
      super.new("Bus TL Model", name, 0);
      this.cfg = cfg;

      this.master_chan = new [this.cfg.n_masters];
      `foreach (this.master_chan,i) begin
         this.master_chan[i] = new("Master Channel", $psprintf("%0d", i));
      end

      this.slave_chan = new [this.cfg.n_slaves];
      `foreach (this.slave_chan,i) begin
         this.slave_chan[i] = new("Slave Channel", $psprintf("%0d", i));
      end

      this.EXECUTED = this.notify.configure();
   endfunction: new

   virtual task main();
      super.main();

      forever begin
         bus_tr tr, slv_tr;
         int initiator, target;
         event avail;
         int candidates[$];
         bit do_continue;
         do_continue = 0;

         // Wait until a transaction is available from one of the masters
         `foreach (this.master_chan,i) begin
            automatic int j = i;
            fork
               begin
                  this.wait_if_stopped_or_empty(this.master_chan[j]);
                  -> avail;
               end
            join_none
         end
         @ (avail);
         disable fork;
         
         // Randomly pick one of the master with an available transaction
         `ifdef INCA
         for(int i=0; i<this.master_chan.size(); ++i) begin
           if(this.master_chan[i].size()>0) candidates.push_back(i);
         end
         `else
         candidates = this.master_chan.find_index() with (item.size() > 0);
         `endif

         if (candidates.size() == 0) begin
            `vmm_fatal(log, "Internal error: no candidates");
            do_continue=1;
         end
         if (!do_continue) begin
         initiator = candidates[{$random} % candidates.size()];
         this.master_chan[initiator].activate(tr);

         $cast(slv_tr, tr.copy());

         // Forward it to the targetted slave, based on the high-order
         // address bits
         target = tr.addr[31:16] % this.cfg.n_slaves;

         `vmm_trace(log, $psprintf("Starting %0d->%0d %s", initiator, target,
                                   tr.psdisplay()));

         void'(this.master_chan[initiator].start());
         this.slave_chan[target].put(slv_tr);

         // Once the slave responds, send the response back to the master
         slv_tr.notify.wait_for(vmm_data::ENDED);
         tr.data   = slv_tr.data;
         tr.status = slv_tr.status;
         void'(this.master_chan[initiator].complete());

         `vmm_trace(log, $psprintf("Completed %0d->%0d %s", initiator, target,
                                   tr.psdisplay()));

         this.notify.indicate(this.EXECUTED, tr);

         void'(this.master_chan[initiator].remove());
         end // if !do_continue
      end
   endtask: main
endclass: bus_model

`endif
