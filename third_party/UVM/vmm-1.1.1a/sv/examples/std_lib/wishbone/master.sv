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


typedef class wb_master;
  
virtual class wb_master_callbacks extends vmm_xactor_callbacks;

   virtual task pre_cycle(wb_master xactor,
                          wb_cycle  cycle,
                          ref bit   drop);
   endtask

   virtual task post_cycle(wb_master xactor,
                           /*const*/ wb_cycle  cycle);
   endtask

endclass: wb_master_callbacks

   
class wb_master extends vmm_xactor;

   virtual wb_if.master sigs;

   wb_cycle_channel exec_chan;

   local wb_cfg cfg;
   local wb_cfg hard_rst_cfg;


   extern function new(string               inst,
                       int unsigned         stream_id,
                       wb_cfg               cfg,
                       virtual wb_if.master sigs,
                       wb_cycle_channel     exec_chan = null);  

   extern virtual function void reconfigure(wb_cfg   cfg);

   extern virtual function void reset_xactor(reset_e rst_typ = SOFT_RST);

   extern protected virtual task main();

   // Example 4-30
   extern protected virtual task read(input  bit [63:0] addr,
                                      output bit [63:0] data,
                                      input  bit [ 7:0] sel,
                                      input  bit [15:0] tgc,
                                      input  bit [15:0] tga,
                                      output bit [15:0] tgd,
                                      input  bit        lock,
                                      output wb_cycle::status_e status);

   extern protected virtual task write(input  bit [63:0] addr,
                                       input  bit [63:0] data,
                                       input  bit [ 7:0] sel,
                                       input  bit [15:0] tgc,
                                       input  bit [15:0] tga,
                                       input  bit [15:0] tgd,
                                       input  bit        lock,
                                       output wb_cycle::status_e status);
endclass: wb_master


function wb_master::new(string               inst,
                        int unsigned         stream_id,
                        wb_cfg               cfg,
                        virtual wb_if.master sigs,
                        wb_cycle_channel     exec_chan = null);
   super.new("Wishbone Master", inst, stream_id);

   this.cfg = cfg;
   this.hard_rst_cfg = cfg;

   this.sigs = sigs;

   if (exec_chan == null) exec_chan = new("Wishbone Master Execution Channel", inst);
   this.exec_chan = exec_chan;

   this.log.is_above(this.exec_chan.log);

   // In-order, blocking execution model
   this.exec_chan.reconfigure(1, 0);
endfunction: new

  
function void wb_master::reconfigure(wb_cfg   cfg);
   this.cfg = cfg;
endfunction: reconfigure


function void wb_master::reset_xactor(reset_e rst_typ = SOFT_RST);
   super.reset_xactor(rst_typ);

   this.sigs.mck.wdat <= 'bz;
   this.sigs.mck.wtgd <= 'bz;
   this.sigs.mck.adr  <= 'bz;
   this.sigs.mck.we   <= 'bz;
   this.sigs.mck.cyc  <= 'bz;
   this.sigs.mck.lock <= 'bz;
   this.sigs.mck.sel  <= 'bz;
   this.sigs.mck.stb  <= 'bz;
   this.sigs.mck.tga  <= 'bz;
   this.sigs.mck.tgc  <= 'bz;
   this.sigs.mck.cti  <= 'bz;
   this.sigs.mck.bte  <= 'bz;
     
   this.exec_chan.flush();

   if (rst_typ >= HARD_RST) begin
      this.cfg = this.hard_rst_cfg;
   end
endfunction: reset_xactor


task wb_master::main();
   fork
      super.main();
   join_none

   forever begin
      wb_cycle tr;
      bit drop = 0;

      this.sigs.mck.wdat  <= 'bz;
      this.sigs.mck.wtgd  <= 'bz;
      this.sigs.mck.adr  <= 'bz;
      this.sigs.mck.cyc  <= 'bz;
      this.sigs.mck.lock <= 'bz;
      this.sigs.mck.sel  <= 'bz;
      this.sigs.mck.stb  <= 'bz;
      this.sigs.mck.tga  <= 'bz;
      this.sigs.mck.tgc  <= 'bz;
      this.sigs.mck.cti  <= 'bz;
      this.sigs.mck.bte  <= 'bz;

      this.wait_if_stopped_or_empty(this.exec_chan);
      this.exec_chan.activate(tr);

      tr.status = wb_cycle::UNKNOWN ;

      `vmm_callback(wb_master_callbacks,
                    pre_cycle(this, tr, drop));
      if (drop) begin
         void'(this.exec_chan.remove());
         continue;
      end

      if (tr.next_cycle !== wb_cycle::CLASSIC ||
          (tr.kind !== wb_cycle::READ && tr.kind != wb_cycle::WRITE )) begin
         `vmm_error(this.log, "Only single read/write classic cycles are supported");
         void'(this.exec_chan.remove());
         continue;
      end

      void'(this.exec_chan.start());

      case (tr.kind)
      wb_cycle::READ : this.read(tr.addr, tr.data, tr.sel,
                                 tr.tgc, tr.tga, tr.tgd, tr.lock,
                                 tr.status);
      wb_cycle::WRITE : this.write(tr.addr, tr.data, tr.sel,
                                   tr.tgc, tr.tga, tr.tgd, tr.lock,
                                   tr.status);
      endcase

      void'(this.exec_chan.complete());
      `vmm_trace(this.log, tr.psdisplay("Completed: "));

      `vmm_callback(wb_master_callbacks,
                    post_cycle(this, tr));

      void'(this.exec_chan.remove());
   end
endtask: main


task wb_master::read(input  bit [63:0] addr,
                     output bit [63:0] data,
                     input  bit [ 7:0] sel,
                     input  bit [15:0] tgc,
                     input  bit [15:0] tga,
                     output bit [15:0] tgd,
                     input  bit        lock,
                     output wb_cycle::status_e status);

   // Section 3.2.1 of Wishbone B3 Specification
   @(this.sigs.mck);

   // Edge 0
   this.sigs.mck.adr <= addr;
   this.sigs.mck.tga <= tga;
   this.sigs.mck.we  <= 1'b0;
   this.sigs.mck.sel <= sel;
   this.sigs.mck.cyc <= 1'b1;
   this.sigs.mck.tgc <= tgc;
   this.sigs.mck.stb <= 1'b1;

   // Edge 1
   status = wb_cycle::TIMEOUT ;
   repeat (this.cfg.max_n_wss + 1) begin
      // Wait states
      @(this.sigs.mck);

      case (1'b1)
      this.sigs.mck.err: status = wb_cycle::ERR ;
      this.sigs.mck.rty: status = wb_cycle::RTY ;
      this.sigs.mck.ack: status = wb_cycle::ACK ;
      default: continue;
      endcase

      break;
   end
   if (status == wb_cycle::TIMEOUT ) begin
      `vmm_error(this.log, "Timeout waiting for ACK_I, RTY_I or ERR_I");
   end
   data = this.sigs.mck.rdat;
   tgd  = this.sigs.mck.rtgd;

   this.sigs.mck.lock <= lock;
   this.sigs.mck.cyc  <= lock;
endtask: read


task wb_master::write(input  bit [63:0] addr,
                      input  bit [63:0] data,
                      input  bit [ 7:0] sel,
                      input  bit [15:0] tgc,
                      input  bit [15:0] tga,
                      input  bit [15:0] tgd,
                      input  bit        lock,
                      output wb_cycle::status_e status);

   // Section 3.2.2 of Wishbone B3 Specification
   @(this.sigs.mck);

   // Edge 0
   this.sigs.mck.adr  <= addr;
   this.sigs.mck.tga  <= tga;
   this.sigs.mck.wdat <= data;
   this.sigs.mck.wtgd <= tgd;
   this.sigs.mck.we   <= 1'b1;
   this.sigs.mck.sel  <= sel;
   this.sigs.mck.cyc  <= 1'b1;
   this.sigs.mck.tgc  <= tgc;
   this.sigs.mck.stb  <= 1'b1;

   // Edge 1
   status = wb_cycle::TIMEOUT ;
   repeat (this.cfg.max_n_wss + 1) begin
      // Wait states
      @(this.sigs.mck);

      case (1'b1)
      this.sigs.mck.err: status = wb_cycle::ERR ;
      this.sigs.mck.rty: status = wb_cycle::RTY ;
      this.sigs.mck.ack: status = wb_cycle::ACK ;
      default: continue;
      endcase

      break;
   end
   if (status == wb_cycle::TIMEOUT ) begin
      `vmm_error(this.log, "Timeout waiting for ACK_I, RTY_I or ERR_I");
   end

   this.sigs.mck.lock <= lock;
   this.sigs.mck.cyc  <= lock;
endtask: write

