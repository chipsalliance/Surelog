//
// Template for VMM-compliant half-duplex physical-level transactor
//
// <XACT>       Name of transactor
// <IF>         Name of physical interface
// <master>     Name of modport in physical interface
// <TR>         Name of input transaction descriptor class
//

`ifndef XACT__SV
`define XACT__SV

`include "vmm.sv"
`include "IF.sv"
`include "TR.sv"

typedef class XACT;

class XACT_callbacks extends vmm_xactor_callbacks;

  // ToDo: Add additional relevant callbacks
  // ToDo: Use "function void" if callbacks cannot be blocking

   // Called before a transaction is executed
   virtual task pre_trans(XACT xactor,
                          TR tr,
                          ref bit drop);
   endtask: pre_trans

   // Called after a transaction has been executed
   virtual task post_trans(XACT xactor,
                           TR tr);
   endtask: post_trans
endclass:XACT_callbacks


class XACT_cfg;
   // ToDo: Add transactor configuration class properties
   rand int mode;
endclass:XACT_cfg


class XACT extends vmm_xactor;

   int EXECUTING;

   protected XACT_cfg cfg;
   local     XACT_cfg reset_cfg;

   TR_channel in_chan;
   virtual IF.master sigs;

   extern function new(string             inst,
                       int                stream_id,
                       virtual IF.master  sigs,
                       XACT_cfg           cfg = null,
                       TR_channel         in_chan = null);
  
   extern virtual function void reconfigure(XACT_cfg cfg);
   extern virtual function void reset_xactor(reset_e rst_typ = SOFT_RST);
   extern protected virtual task main();

endclass:XACT


function XACT::new(string             inst,
                   int                stream_id,
                   virtual IF.master  sigs,
                   XACT_cfg           cfg,
                   TR_channel         in_chan);

   super.new("XACT Transactor", inst, stream_id);

   this.EXECUTING = this.notify.configure(-1, vmm_notify::ON_OFF);

   this.sigs = sigs;

   if (cfg == null) cfg = new;
   this.cfg = cfg;
   this.reset_cfg = cfg;

   if (in_chan == null) in_chan = new("XACT Input Channel", inst);
   this.in_chan = in_chan;
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

   // ToDo: Reset output signals
   this.sigs.mck1.sync_txd <= 0;
   this.sigs.mck1.sync_dat <= 'z;
   this.sigs.async_en      <= 0;

   this.in_chan.flush();

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
   end
endfunction: reset_xactor


task XACT::main();
   super.main();

   forever begin
      TR tr;
      bit drop;

      // ToDo: Set output signals to their idle state
      this.sigs.mck1.sync_txd <= 0;
      this.sigs.mck1.sync_dat <= 'z;
      this.sigs.async_en      <= 0;
      
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

      case (tr.kind) 
         TR::READ: begin
            // ToDo: Implement READ transaction
         end

         TR::WRITE: begin
            // ToDo: Implement WRITE transaction
         end
      endcase

      this.notify.reset(this.EXECUTING);
      void'(this.in_chan.complete());

      `vmm_trace(this.log, "Completed transaction...");
      `vmm_debug(this.log, tr.psdisplay("   "));

      `vmm_callback(XACT_callbacks,
                    post_trans(this, tr));

      void'(this.in_chan.remove());
   end
endtask: main

`endif
