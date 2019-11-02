//
// Template for VMM-compliant full-duplex functional-level transactor
//
// <XACT>       Name of transactor
// <TR>         Name of high-level transaction descriptor class
// <TX>         Name of low-level transaction descriptor class
//

`ifndef XACT__SV
`define XACT__SV

`include "vmm.sv"
`include "TR.sv"
`include "TX.sv"

typedef class XACT;

class XACT_callbacks extends vmm_xactor_callbacks;

  // ToDo: Add additional relevant callbacks
  // ToDo: Use task if callbacks can be blocking

    // Called before a transaction is executed
   virtual task pre_trans(XACT xactor,
                          TR tr,
                          bit drop);
   endtask: pre_trans

   virtual function void pre_trans_exec(XACT xactor,
                                        TR tr,
                                        TX tx[$]);
   endfunction: pre_trans_exec

   // Called at start of lower transaction
   virtual task pre_exec(XACT xactor,
                         TX tr,
                         bit drop);
   endtask: pre_exec

   // Called at end of lower transaction
   virtual task post_exec(XACT xactor,
                          TX tr);
   endtask: post_exec

   virtual function void post_trans_exec(XACT xactor,
                                         TR tr,
                                         TX tx[$]);
   endfunction: post_trans_exec

   // Called after a transaction has been executed
   virtual task post_in_trans(XACT xactor,
                              TR tr);
   endtask: post_in_trans

   // Called at end of observed lower-level transaction
   virtual function void post_trans_obs(XACT xactor,
                                        TX tx,
                                        bit drop);
   endfunction: post_trans_obs

   // Call when a high-level transaction has been identified
   virtual function void post_out_trans(XACT xactor,
                                        TX tx[$],
                                        TR tr,
                                        bit drop);
   endfunction: post_out_trans
endclass:XACT_callbacks


class XACT_cfg;
   // ToDo: Add transactor configuration class properties
   rand int mode;
endclass: XACT_cfg


class XACT extends vmm_xactor;

  int EXECUTING;
  int SUB_EXECUTING;
  int OBSERVED;
  int SUB_OBSERVED;
  
  protected XACT_cfg cfg;
  local     XACT_cfg reset_cfg;
  protected TR       rx_factory;
  local     TR       reset_rx_factory;

  TR_channel in_chan;
  TR_channel out_chan;
  TX_channel exec_chan;
  TX_channel obs_chan;

  extern function new (string     inst,
                       int        stream_id,
                       XACT_cfg   cfg = null,
                       TR_channel in_chan = null,
                       TR_channel out_chan = null,
                       TX_channel exec_chan = null,
                       TX_channel obs_chan = null,
                       TR         rx_factory = null);
  
  extern virtual function void reconfigure(XACT_cfg cfg);
  extern virtual function void reset_xactor(reset_e rst_typ = SOFT_RST);
  extern protected virtual task main();
  extern protected virtual task tx_driver();
  extern protected virtual task rx_monitor();

endclass:XACT


function XACT::new(string     inst,
                   int        stream_id,
                   XACT_cfg   cfg,
                   TR_channel in_chan,
                   TR_channel out_chan,
                   TX_channel exec_chan,
                   TX_channel obs_chan,
                   TR         rx_factory);

   super.new("XACT Transactor", inst, stream_id);

   this.EXECUTING     = this.notify.configure(-1, vmm_notify::ON_OFF);
   this.SUB_EXECUTING = this.notify.configure(-1, vmm_notify::ON_OFF);
   this.OBSERVED      = this.notify.configure();
   this.SUB_OBSERVED  = this.notify.configure();

   if (cfg == null) cfg = new;
   this.cfg = cfg;
   this.reset_cfg = cfg;

   if (in_chan == null) in_chan = new("XACT Input Channel", inst);
   this.in_chan = in_chan;
   if (out_chan == null) out_chan = new("XACT Output Channel", inst);
   this.out_chan = out_chan;
   if (exec_chan == null) exec_chan = new("XACT Execution Channel", inst);
   this.exec_chan = exec_chan;
   if (obs_chan == null) obs_chan = new("XACT Observation Channel", inst);
   this.obs_chan = obs_chan;

   if (rx_factory == null) rx_factory = new;
   this.rx_factory = rx_factory;
   this.reset_rx_factory = rx_factory;
endfunction: new


function void XACT::reconfigure(XACT_cfg cfg);

   if (!this.notify.is_on(XACTOR_IDLE)) begin
      `vmm_warning(this.log, "Transactor should be reconfigured only when IDLE");
   end

   this.cfg = cfg;
   
   // ToDo: Notify any running threads of the new configuration
endfunction: reconfigure


function void XACT::reset_xactor(reset_e rst_typ);

   super.reset_xactor(rst_typ);

   this.in_chan.flush();
   this.out_chan.flush();
   this.exec_chan.flush();
   this.obs_chan.flush();

   // ToDo: Reset other state information

   if (rst_typ != SOFT_RST) begin
      // ToDo: Reset state if FIRM or above
   end

   if (rst_typ == PROTOCOL_RST) begin
      // ToDo: Reset state if PROTOCOL
   end
   
   if (rst_typ == HARD_RST) begin
      // ToDo: Reset state if HARD or above
      this.cfg = this.reset_cfg;
      this.rx_factory = this.reset_rx_factory;
   end
endfunction:reset_xactor


task XACT::main();
   super.main();

   fork
      tx_driver();
      rx_monitor();
   join
endtask:main


task XACT::tx_driver();

   forever begin
      TR tr;
      TX tx[$];
      bit drop;

      this.wait_if_stopped_or_empty(this.in_chan);
      this.in_chan.activate(tr);

      drop = 0;
      `vmm_callback(XACT_callbacks,
                    pre_trans(this, tr, drop));
      if (drop) begin
         void'(this.in_chan.remove());
         continue;
      end
   
      void'(this.in_chan.start());
      this.notify.indicate(this.EXECUTING, tr);

      `vmm_trace(this.log, "Starting transaction...");
      `vmm_debug(this.log, tr.psdisplay("   "));

      // ToDo: Turn high-level transaction into a series of
      //       low-level transactions

      `vmm_callback(XACT_callbacks,
                    pre_trans_exec(this, tr, tx));

      foreach (tx[i]) begin
         drop = 0;
         `vmm_callback(XACT_callbacks,
                       pre_exec(this, tx[i], drop));
         if (drop) continue;

         this.notify.indicate(this.SUB_EXECUTING, tx[i]);

         `vmm_debug(this.log, "Executing lower-level transaction...");
         `vmm_verbose(this.log, tx[i].psdisplay("   "));
         
         this.exec_chan.put(tx[i]);

         // ToDo: Add completion model if not blocking
         
         this.notify.reset(this.SUB_EXECUTING);

         `vmm_debug(this.log, "Executed lower-level transaction...");
         `vmm_verbose(this.log, tx[i].psdisplay("   "));
         
         `vmm_callback(XACT_callbacks,
                       post_exec(this, tx[i]));
      end

      `vmm_callback(XACT_callbacks,
                    post_trans_exec(this, tr, tx));

      // ToDo: Determine result of high-level transaction from the
      //       results of the low-level transactions

      this.notify.reset(this.EXECUTING);
      void'(this.in_chan.complete());

      `vmm_trace(this.log, "Completed transaction...");
      `vmm_debug(this.log, tr.psdisplay("   "));

      `vmm_callback(XACT_callbacks,
                    post_in_trans(this, tr));

      void'(this.in_chan.remove());
   end
endtask: tx_driver


task XACT::rx_monitor();

   forever begin
      TR tr;
      TX tx[$];
      TX tmp_tx;
      bit drop;

      tr = null;
      
      this.wait_if_stopped_or_empty(this.obs_chan);
      this.obs_chan.get(tmp_tx);
      tx.push_back(tmp_tx);

      drop = 0;
      `vmm_callback(XACT_callbacks,
                    post_trans_obs(this, tx[tx.size()-1], drop));
      if (drop) begin
         tx.pop_back();
         continue;
      end
   
      this.notify.indicate(this.SUB_OBSERVED, tx[tx.size()-1]);

      `vmm_debug(this.log, "Observed lower-level transaction...");
      `vmm_verbose(this.log, tx[tx.size()-1].psdisplay("   "));

      // ToDo: Check if the lower-level transactions observed so far
      //       create a higher-level transaction

      $cast(tr, this.rx_factory.copy());
      
      if (tr != null) begin
         drop = 0;
         
         `vmm_callback(XACT_callbacks,
                       post_out_trans(this, tx, tr, drop));

         if (!drop) begin
            this.notify.indicate(this.OBSERVED, tr);

            `vmm_trace(this.log, "Observed transaction...");
            `vmm_debug(this.log, tr.psdisplay("   "));
         
            this.out_chan.sneak(tr);
         end

         // ToDo: removed the interpreted observed sub transactions
         tx.delete();
      end
   end
endtask: rx_monitor

`endif
