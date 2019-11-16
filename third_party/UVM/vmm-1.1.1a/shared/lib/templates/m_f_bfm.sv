//
// Template for VMM-compliant full-duplex physical-level monitor
//
// <XACT>       Name of transactor
// <IF>         Name of physical interface
// <passive>    Name of modport in physical interface
// <TR>         Name of input/output transaction descriptor class
//

`ifndef XACT__SV
`define XACT__SV

`include "vmm.sv"
`include "IF.sv"
`include "TR.sv"

typedef class XACT;

class XACT_callbacks extends vmm_xactor_callbacks;

   // ToDo: Add additional relevant callbacks
   // ToDo: Use a task if callbacks can be blocking

   // Called at start of observed transaction
   virtual function void pre_tx_trans(XACT xactor,
                                      TR tr);
   endfunction: pre_tx_trans

   // Called at end of observed transaction
   virtual function void post_tx_trans(XACT xactor,
                                       TR tr);
   endfunction: post_tx_trans

   // Called at start of observed transaction
   virtual function void pre_rx_trans(XACT xactor,
                                      TR tr);
   endfunction: pre_rx_trans

   // Called at end of observed transaction
   virtual function void post_rx_trans(XACT xactor,
                                       TR tr);
   endfunction: post_rx_trans
endclass:XACT_callbacks


class XACT_cfg;
   // ToDo: Add transactor configuration class properties
   rand int mode;
endclass:XACT_cfg


class XACT extends vmm_xactor;

  int OBS_ON_TX;
  int OBS_ON_RX;
  
  protected XACT_cfg cfg;
  local     XACT_cfg reset_cfg;
  protected TR tx_factory;
  local     TR reset_tx_factory;
  protected TR rx_factory;
  local     TR reset_rx_factory;

  TR_channel tx_chan;
  TR_channel rx_chan;
  virtual IF.passive sigs;

  extern function new(string              inst,
                      int                 stream_id,
                      virtual IF.passive  sigs,
                      XACT_cfg   cfg = null,
                      TR_channel tx_chan = null,
                      TR_channel rx_chan = null,
                      TR         tx_factory = null,
                      TR         rx_factory = null);
  
  extern virtual function void reconfigure(XACT_cfg cfg);
  extern virtual function void reset_xactor(reset_e rst_typ = SOFT_RST);
  extern protected virtual task main();
  extern protected virtual task tx_monitor();
  extern protected virtual task rx_monitor();

endclass:XACT


function XACT::new(string              inst,
                   int                 stream_id,
                   virtual IF.passive  sigs,
                   XACT_cfg   cfg,
                   TR_channel tx_chan,
                   TR_channel rx_chan,
                   TR         tx_factory,
                   TR         rx_factory);

   super.new("XACT Transactor", inst, stream_id);

   this.OBS_ON_TX = this.notify.configure(-1, vmm_notify::ON_OFF);
   this.OBS_ON_RX = this.notify.configure(-1, vmm_notify::ON_OFF);

   this.sigs = sigs;

   if (cfg == null) cfg = new;
   this.cfg = cfg;
   this.reset_cfg = cfg;

   if (tx_chan == null) tx_chan = new("XACT Tx Channel", inst);
   this.tx_chan = tx_chan;
   if (rx_chan == null) rx_chan = new("XACT Rx Channel", inst);
   this.rx_chan = rx_chan;

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

      // ToDo: Wait for start of transaction

      $cast(tr, this.tx_factory.copy());
      `vmm_callback(XACT_callbacks,
                    pre_tx_trans(this, tr));

      tr.notify.indicate(vmm_data::STARTED);
      this.notify.indicate(this.OBS_ON_TX, tr);

      `vmm_trace(this.log, "Starting Tx transaction...");

      // ToDo: Observe transaction

      `vmm_trace(this.log, "Completed Tx transaction...");
      `vmm_debug(this.log, tr.psdisplay("   "));

      this.notify.reset(this.OBS_ON_TX);
      tr.notify.indicate(vmm_data::ENDED);

      `vmm_callback(XACT_callbacks,
                    post_tx_trans(this, tr));

      this.tx_chan.sneak(tr);
   end
endtask: tx_monitor


task XACT::rx_monitor();

   forever begin
      TR tr;

      // ToDo: Wait for start of transaction

      $cast(tr, this.rx_factory.copy());
      `vmm_callback(XACT_callbacks,
                    pre_rx_trans(this, tr));

      tr.notify.indicate(vmm_data::STARTED);
      this.notify.indicate(this.OBS_ON_RX, tr);

      `vmm_trace(this.log, "Starting Rx transaction...");

      // ToDo: Observe transaction

      `vmm_trace(this.log, "Completed Tx transaction...");
      `vmm_debug(this.log, tr.psdisplay("   "));

      this.notify.reset(this.OBS_ON_RX);
      tr.notify.indicate(vmm_data::ENDED);

      `vmm_callback(XACT_callbacks,
                    post_rx_trans(this, tr));

      this.rx_chan.sneak(tr);
   end
endtask: rx_monitor

`endif
