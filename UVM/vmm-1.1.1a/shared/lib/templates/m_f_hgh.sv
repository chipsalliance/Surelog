//
// Template for VMM-compliant full-duplex functional-level monitor
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
  // ToDo: Use a task if callbacks can be blocking

   // Called at end of observed lower-level transaction
   virtual function void post_tx_trans_obs(XACT xactor,
                                  TX tx,
                                  bit drop);
   endfunction: post_tx_trans_obs
   virtual function void post_rx_trans_obs(XACT xactor,
                                  TX tx,
                                  bit drop);
   endfunction: post_rx_trans_obs

   // Call when a high-level transaction has been identified
   virtual function void post_tx_trans(XACT xactor,
                                       TX tx[$],
                                       TR tr,
                                       bit drop);
   endfunction: post_tx_trans
   virtual function void post_rx_trans(XACT xactor,
                                       TX tx[$],
                                       TR tr,
                                       bit drop);
   endfunction: post_rx_trans
endclass:XACT_callbacks


class XACT_cfg;
   // ToDo: Add transactor configuration class properties
   rand int mode;
endclass:XACT_cfg


class XACT extends vmm_xactor;

  int OBS_TX;
  int SUB_OBS_TX;
  int OBS_RX;
  int SUB_OBS_RX;
  
  protected XACT_cfg cfg;
  local     XACT_cfg reset_cfg;
  protected TR tx_factory;
  local     TR reset_tx_factory;
  protected TR rx_factory;
  local     TR reset_rx_factory;

  TR_channel tx_chan;
  TR_channel rx_chan;
  TX_channel tx_obs_chan;
  TX_channel rx_obs_chan;

  extern function new (string     inst,
                       int        stream_id,
                       XACT_cfg   cfg = null,
                       TR_channel tx_chan = null,
                       TR_channel rx_chan = null,
                       TX_channel tx_obs_chan = null,
                       TX_channel rx_obs_chan = null,
                       TR         tx_factory = null,
                       TR         rx_factory = null);
  
  extern virtual function void reconfigure(XACT_cfg cfg);
  extern virtual function void reset_xactor(reset_e rst_typ = SOFT_RST);
  extern protected virtual task main();
  extern protected virtual task tx_monitor();
  extern protected virtual task rx_monitor();

endclass:XACT


function XACT::new(string     inst,
                   int        stream_id,
                   XACT_cfg   cfg,
                   TR_channel tx_chan,
                   TR_channel rx_chan,
                   TX_channel tx_obs_chan,
                   TX_channel rx_obs_chan,
                   TR         tx_factory,
                   TR         rx_factory);

   super.new("XACT Transactor", inst, stream_id);

   this.OBS_TX     = this.notify.configure();
   this.SUB_OBS_TX = this.notify.configure();
   this.OBS_RX     = this.notify.configure();
   this.SUB_OBS_RX = this.notify.configure();

   if (cfg == null) cfg = new;
   this.cfg = cfg;
   this.reset_cfg = cfg;

   if (tx_chan == null) tx_chan = new("XACT Tx Output Channel", inst);
   this.tx_chan = tx_chan;
   if (rx_chan == null) rx_chan = new("XACT Rx Output Channel", inst);
   this.rx_chan = rx_chan;
   if (tx_obs_chan == null) tx_obs_chan = new("XACT Tx Observation Channel", inst);
   this.tx_obs_chan = tx_obs_chan;
   if (rx_obs_chan == null) rx_obs_chan = new("XACT Rx Observation Channel", inst);
   this.rx_obs_chan = rx_obs_chan;

   if (tx_factory == null) tx_factory = new;
   this.tx_factory = tx_factory;
   this.reset_tx_factory = tx_factory;
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

   this.tx_chan.flush();
   this.rx_chan.flush();
   this.tx_obs_chan.flush();
   this.rx_obs_chan.flush();

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
      this.tx_factory = this.reset_tx_factory;
      this.rx_factory = this.reset_rx_factory;
   end
endfunction: reset_xactor


task XACT::main();
   super.main();

   fork
      tx_monitor();
      rx_monitor();
   join
endtask: main


task XACT::tx_monitor();

   forever begin
      TR tr;
      TX tx[$];
      TX tmp_tx;
      bit drop;

      tr = null;
      
      this.wait_if_stopped_or_empty(this.tx_obs_chan);
      this.tx_obs_chan.get(tmp_tx);
      tx.push_back(tmp_tx);

      drop = 0;
      `vmm_callback(XACT_callbacks,
                    post_tx_trans_obs(this, tx[tx.size()-1], drop));
      if (drop) begin
         tx.pop_back();
         continue;
      end
   
      this.notify.indicate(this.SUB_OBS_TX, tx[tx.size()-1]);

      `vmm_debug(this.log, "Observed lower-level Tx transaction...");
      `vmm_verbose(this.log, tx[tx.size()-1].psdisplay("   "));

      // ToDo: Check if the lower-level transactions observed so far
      //       create a higher-level transaction

      $cast(tr, this.tx_factory.copy());
      
      if (tr != null) begin
         drop = 0;
         
         `vmm_callback(XACT_callbacks,
                       post_tx_trans(this, tx, tr, drop));

         if (!drop) begin
            this.notify.indicate(this.OBS_TX, tr);

            `vmm_trace(this.log, "Observed transaction...");
            `vmm_debug(this.log, tr.psdisplay("   "));
         
            this.tx_chan.sneak(tr);
         end

         // ToDo: removed the interpreted observed sub transactions
         tx.delete();
      end
   end
endtask: tx_monitor


task XACT::rx_monitor();

   forever begin
      TR tr;
      TX tx[$];
      TX tmp_tx;
      bit drop;

      tr = null;
      
      this.wait_if_stopped_or_empty(this.rx_obs_chan);
      this.rx_obs_chan.get(tmp_tx);
      tx.push_back(tmp_tx);

      drop = 0;
      `vmm_callback(XACT_callbacks,
                    post_rx_trans_obs(this, tx[tx.size()-1], drop));
      if (drop) begin
         tx.pop_back();
         continue;
      end
   
      this.notify.indicate(this.SUB_OBS_RX, tx[tx.size()-1]);

      `vmm_debug(this.log, "Observed lower-level Rx transaction...");
      `vmm_verbose(this.log, tx[tx.size()-1].psdisplay("   "));

      // ToDo: Check if the lower-level transactions observed so far
      //       create a higher-level transaction

      $cast(tr, this.rx_factory.copy());
      
      if (tr != null) begin
         drop = 0;
         
         `vmm_callback(XACT_callbacks,
                       post_rx_trans(this, tx, tr, drop));

         if (!drop) begin
            this.notify.indicate(this.OBS_RX, tr);

            `vmm_trace(this.log, "Observed transaction...");
            `vmm_debug(this.log, tr.psdisplay("   "));
         
            this.rx_chan.sneak(tr);
         end

         // ToDo: removed the interpreted observed sub transactions
         tx.delete();
      end
   end
endtask: rx_monitor

`endif
