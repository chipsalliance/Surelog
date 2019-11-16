//
// Template for physical access BFM that can be used by RAL
//
// <XACT>       Name of physical-level transactor
// <TR>         Name of physical-level transaction descriptor class
// <VIF>        Name of virtual interface used by transactor
// [filename]   XACT_ral_bfm
//

`ifndef XACT_RAL_BFM__SV
`define XACT_RAL_BFM__SV

`include "XACT.sv"
`include "vmm_ral.sv"

class XACT_ral_bfm extends vmm_rw_xactor;
   XACT bfm;

   function new(string        inst,
                int unsigned  stream_id,
                virtual VIF   sigs);
      super.new("XACT RAL BFM", inst, stream_id);

      this.bfm = new(inst, stream_id, sigs);
   endfunction: new


   virtual function void start_xactor();
      super.start_xactor();
      this.bfm.start_xactor();
   endfunction

   
   virtual function void stop_xactor();
      super.stop_xactor();
      this.bfm.stop_xactor();
   endfunction

   
   virtual function void reset_xactor(vmm_xactor::reset_e rst_typ = vmm_xactor::SOFT_RST);
      super.reset_xactor(rst_typ);
      this.bfm.reset_xactor(rst_typ);
   endfunction

   
   virtual task execute_single(vmm_rw_access tr);
      TR cyc;
      
      // ToDo: Translate the generic RW into a simple RW
      cyc = new;
      if (tr.kind == vmm_rw::WRITE) begin
         // Write cycle
         // ...
      end
      else begin
         // Read cycle
         // ...
      end

      this.bfm.in_chan.put(cyc);

      // ToDo: Send the result of read cycles back to the RAL
      if (tr.kind == vmm_rw::READ) begin
         tr.data = ...
      end
   endtask: execute_single
endclass: XACT_ral_bfm

`endif
