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


`ifndef APB_SLAVE__SV
`define APB_SLAVE__SV

`include "apb_if.sv"
`include "apb_rw.sv"

class apb_slave_cfg;
   rand bit [31:0] start_addr = 32'h0000_0000;
   rand bit [31:0] end_addr   = 32'hFFFF_FFFF;

   constraint apb_slave_cfg_valid {
                                   end_addr >= start_addr;
   }

   virtual function string psdisplay(string prefix = "");
      $sformat(psdisplay, "%sAPB Slave Config: ['h%h-'h%h]",
               prefix, this.start_addr, this.end_addr);
   endfunction: psdisplay
endclass: apb_slave_cfg

typedef class apb_slave;
class apb_slave_cbs extends vmm_xactor_callbacks;
   virtual function void pre_response(apb_slave xact,
                                      apb_rw    cycle);
   endfunction: pre_response

   virtual function void post_response(apb_slave xactor,
                                       apb_rw    cycle);
   endfunction: post_response
     endclass: apb_slave_cbs

class apb_slave extends vmm_xactor;
   virtual apb_if.slave sigs;
   local apb_slave_cfg cfg;
   apb_rw_channel resp_chan;
   typedef enum {RESPONSE} notifications_e;

   apb_rw tr_factory;

   local bit [31:0] ram[*];

   function new(string               name,
                int unsigned         stream_id,
                virtual apb_if.slave sigs,
                apb_slave_cfg        cfg = null,
                apb_rw_channel       resp_chan = null,
                apb_rw               tr_factory = null);
      super.new("APB Slave", name, stream_id);
      this.sigs = sigs;

      if (cfg == null) cfg = new;
      this.cfg = cfg;
      this.resp_chan = resp_chan;
      if (tr_factory == null) tr_factory = new;
      this.tr_factory = tr_factory;

      void'(this.notify.configure(RESPONSE));
   endfunction: new

   virtual function void reconfigure(apb_slave_cfg cfg);
      this.cfg = cfg;
   endfunction: reconfigure

   virtual function void poke(bit [31:0] addr,
                              bit [31:0] data);
      if (addr < this.cfg.start_addr ||
          addr > this.cfg.end_addr) begin
         `vmm_error(this.log, "Out-of-range poke");
         return;
      end
      this.ram[addr] = data;
endfunction: poke

   virtual function bit [31:0] peek(bit [31:0] addr);
      if (addr < this.cfg.start_addr ||
          addr > this.cfg.end_addr) begin
         `vmm_error(this.log, "Out-of-range peek");
         return 'x;
      end
      return (this.ram.exists(addr)) ? this.ram[addr] : 'x;
endfunction: peek

   virtual function void reset_xactor(reset_e rst_typ = SOFT_RST);
      super.reset_xactor(rst_typ);
      this.resp_chan.flush();
      this.sigs.sck.prdata <= 'z;
   endfunction: reset_xactor

   virtual protected task main();
      super.main();
      forever begin
         bit do_continue=0;
         apb_rw tr;

         this.sigs.sck.prdata <= 'z;
         this.wait_if_stopped();

         `vmm_trace(log, "Waiting for start of transaction...");

         // Wait for a SETUP cycle
         do @ (this.sigs.sck);
         while (this.sigs.sck.psel !== 1'b1 ||
                this.sigs.sck.penable !== 1'b0 ||
                this.sigs.sck.paddr < this.cfg.start_addr ||
                this.sigs.sck.paddr > this.cfg.end_addr);
         $cast(tr, this.tr_factory.allocate());

         tr.notify.indicate(vmm_data::STARTED);
         tr.kind = (this.sigs.sck.pwrite) ?
                      apb_rw::WRITE : apb_rw::READ;
         tr.addr = this.sigs.sck.paddr;

         `vmm_trace(log, {"Responding to transaction...\n",
                          tr.psdisplay("   ")});
         if (tr.kind == apb_rw::READ) begin
            if (this.resp_chan == null) begin
               if (!this.ram.exists(tr.addr)) tr.data = 'x;
               else tr.data = this.ram[tr.addr];
            end
            else begin
               bit abort = 0;
               fork
                  begin
                     fork
                       begin
                          @ (this.sigs.sck);
                          `vmm_error(this.log, "No response in time");
                          abort = 1;
                       end
                       this.resp_chan.put(tr);
                     join_any
                     disable fork;
                  end
               join
               if (abort) do_continue=1;
            end
            if(!do_continue) begin
              `vmm_callback(apb_slave_cbs, pre_response(this, tr));

              this.sigs.sck.prdata <= tr.data;
              @ (this.sigs.sck);
            end
         end
         else begin
            @ (this.sigs.sck);
            tr.data = this.sigs.sck.pwdata;

            `vmm_callback(apb_slave_cbs, pre_response(this, tr));

            if (this.resp_chan == null)
               this.ram[tr.addr] = tr.data;
            else this.resp_chan.sneak(tr);
         end
         if(!do_continue) begin
         if (this.sigs.sck.penable !== 1'b1) begin
            `vmm_error(this.log, "APB protocol violation: SETUP cycle not followed by ENABLE cycle");
         end
         tr.notify.indicate(vmm_data::ENDED);

         `vmm_callback(apb_slave_cbs, post_response(this, tr));

         `vmm_trace(log, {"Responded to transaction...\n",
                          tr.psdisplay("   ")});
         this.notify.indicate(RESPONSE, tr);
         end //do_continue
      end
   endtask: main
endclass: apb_slave

`endif
