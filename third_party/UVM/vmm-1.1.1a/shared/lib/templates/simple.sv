//
// Template for physical access BFM that can be used by RAL
//
//

`ifndef simple_main_RAL_BFM__SV
`define simple_main_RAL_BFM__SV

`include "simple.sv"
`include "vmm_ral.sv"

class simple_main_ral_bfm extends vmm_rw_xactor;
   simple bfm;

   function new(string        inst,
                int unsigned  stream_id,
                simple          bfm);
      super.new("simple RAL Master for main domain", inst, stream_id);

      this.bfm = bfm;
   endfunction: new

   
   virtual task execute_single(vmm_rw_access tr);
      simple_tr cyc;
      
      // ToDo: Translate the generic RW into an appropriate RW
      // for the specified domain
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
endclass: simple_main_ral_bfm

`endif
