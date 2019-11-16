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


typedef class wb_slave;

virtual class wb_slave_callbacks extends vmm_xactor_callbacks;

   virtual task pre_cycle(wb_slave          xactor,
                          wb_cycle          req,
                          ref wb_cycle_resp resp);
   endtask

   virtual task pre_response(wb_slave       xactor,
                             wb_cycle_resp  resp);
   endtask

   virtual task post_cycle(wb_slave      xactor,
                           /*const*/ wb_cycle_resp resp);
   endtask

endclass: wb_slave_callbacks


class wb_slave extends vmm_xactor;

   virtual wb_if.slave sigs;

   wb_cycle req_factory;
   wb_cycle_resp randomized_resp;  // NULL if req/resp channels are used
      
   wb_cycle_channel      req_chan;
   wb_cycle_resp_channel resp_chan;

   protected wb_slave_cfg cfg;
   local wb_slave_cfg hard_rst_cfg;
   local integer data_id;

   extern function new(string                inst,
                       int unsigned          stream_id = -1,
                       wb_slave_cfg          cfg,
                       virtual wb_if.slave   sigs,
                       wb_cycle_channel      req_chan  = null,
                       wb_cycle_resp_channel resp_chan = null,
                       wb_cycle              req_factory = null);
      
   extern virtual function void reconfigure(wb_slave_cfg cfg = null);
      
   extern virtual function void reset_xactor(reset_e rst_typ = SOFT_RST);
      
   extern protected virtual task main();
      
endclass: wb_slave



typedef class wb_ram;

virtual class wb_ram_callbacks extends vmm_xactor_callbacks;

   virtual task pre_response(wb_ram            xactor,
                             wb_cycle          req,
                             ref wb_cycle_resp resp);
   endtask

endclass: wb_ram_callbacks


typedef bit unsigned [63:0] wb_ram_addr_typ;

class wb_ram extends vmm_xactor;

   wb_cycle_resp resp_factory;

   wb_cycle_channel      req_chan;
   wb_cycle_resp_channel resp_chan;

   local bit [63:0] ram[* /*wb_ram_addr_typ*/];


   extern function new(string                inst,
                       int unsigned          stream_id    = -1,
                       wb_cycle_channel      req_chan     = null,
                       wb_cycle_resp_channel resp_chan    = null,
                       wb_cycle_resp         resp_factory = null);

   extern virtual function void reset_xactor(reset_e rst_typ = SOFT_RST);
      
   extern protected virtual task main();
   extern virtual function bit [63:0] read(bit [63:0] addr);
   extern virtual function void write(bit [63:0] addr,
                                      bit [63:0] data);
endclass: wb_ram



//
// wb_slave
//

function wb_slave::new(string                inst,
                       int unsigned          stream_id = -1,
                       wb_slave_cfg          cfg,
                       virtual wb_if.slave   sigs,
                       wb_cycle_channel      req_chan = null,
                       wb_cycle_resp_channel resp_chan = null,
                       wb_cycle              req_factory = null);
   super.new("Wishbone Slave", inst, stream_id);

   this.cfg = cfg;
   this.hard_rst_cfg = cfg;
   
   this.sigs = sigs;
   
   this.req_chan = req_chan;
   this.resp_chan = resp_chan;
   
   this.log.is_above(this.req_chan.log);
   this.log.is_above(this.resp_chan.log);

   if (req_factory == null) req_factory = new;
   this.req_factory = req_factory;
   this.randomized_resp = new(null, null);
   
   this.data_id = 0;
endfunction: new
  
   
function void wb_slave::reconfigure(wb_slave_cfg cfg = null);
   this.cfg = cfg;
endfunction: reconfigure

   
function void wb_slave::reset_xactor(reset_e rst_typ = SOFT_RST);
   super.reset_xactor(rst_typ);

   this.sigs.rdat <= 64'bz;
   this.sigs.rtgd <= 16'bz;
   this.sigs.ack  <=  1'bz;
   this.sigs.rty  <=  1'bz;
   this.sigs.err  <=  1'bz;

   this.req_chan.flush();
   this.resp_chan.flush();

   if (rst_typ >= HARD_RST) begin
      this.cfg = this.hard_rst_cfg;
   end

   this.data_id = 0;
endfunction: reset_xactor

   
task wb_slave::main();
   bit do_break;
   fork
      super.main();
   join_none

   do_break = 0;

   while(!do_break) begin
      wb_cycle req;
      bit do_continue=0;
      
      //
      // From 3.2.1 & 3.2.2 from Wishbone Spec.
      //
      
      // Watch for the begining of a cycle
      // handling back-to-back cycles...
      do begin
         if (this.sigs.cyc !== 1'b1 ||
             this.sigs.stb !== 1'b1) begin
            this.sigs.rdat <= 64'bz;
            this.sigs.rtgd <= 16'bz;
            this.sigs.ack  <=  1'bz;
            this.sigs.rty  <=  1'bz;
            this.sigs.err  <=  1'bz;
         end

         @(this.sigs.cyc or
           this.sigs.stb or
           this.sigs.adr or
           this.sigs.sel or
           this.sigs.we  or
           this.sigs.tga or
           this.sigs.tgc);
      end while (this.sigs.cyc !== 1'b1 ||
                 this.sigs.stb !== 1'b1);

      $cast(req, this.req_factory.allocate());
      req.stream_id = this.stream_id;
      req.data_id   = this.data_id++;

      // Decode qualified input from the master
      req.addr = this.sigs.adr;

      // Are we the target of the cycle?
      if (!(this.cfg.min_addr <= req.addr && req.addr <= this.cfg.max_addr)) do_continue=1;

     if(!do_continue) begin

      // Complete the cycle
      req.tga  = this.sigs.tga;
      if (this.sigs.we) begin
         req.kind = wb_cycle::WRITE ;
         req.data = this.sigs.wdat;
         req.tgd  = this.sigs.wtgd;
      end
      else begin
         req.kind = wb_cycle::READ ;
      end
      req.sel  = this.sigs.sel;
      req.tgc  = this.sigs.tgc;

      // Wait states may be introduced by
      // delays in the response
      this.sigs.ack <= 1'b0;
      this.sigs.rty <= 1'b0;
      this.sigs.err <= 1'b0;

      `vmm_trace(this.log, req.psdisplay("Request: "));

      begin
         integer n_wss = 0;
         wb_cycle_resp resp;
         
         fork
            forever begin
               @ (this.sigs.sck);
               n_wss++;
            end
         join_none

         resp = null;
         `vmm_callback(wb_slave_callbacks,
                       pre_cycle(this, req, resp));

         if (resp == null && this.req_chan != null && this.resp_chan != null) begin
            this.req_chan.put(req);
            this.resp_chan.get(resp);
         end
         if (resp != null) begin
            if (resp.req == null) resp.req = req;
            if (resp.cfg == null) resp.cfg = cfg;
            if (!resp.randomize()) begin
               `vmm_fatal(this.log, "Unable to randomize user-defined cycle response");
               disable fork;
               do_break=1;
            end
         end else begin
            this.randomized_resp.req = req;
            this.randomized_resp.cfg = cfg;
            if (!this.randomized_resp.randomize()) begin
               `vmm_fatal(this.log, "Unable to randomize factory cycle response");
               disable fork;
               do_break=1;
            end
            $cast(resp, this.randomized_resp.copy());
         end
        
         if(!do_break) begin
         // Does this response correspond to our request?
         if (resp.req != req) begin
            if (resp.req.kind != req.kind ||
                resp.req.addr != req.addr) begin
               `vmm_error(this.log,
                          "Response descriptor does not match request");
               do_break=1;
            end
         end
         end //do_break

         if(!do_break) begin
         `vmm_callback(wb_slave_callbacks,
                       pre_response(this, resp));

         disable fork;

         `vmm_trace(this.log, resp.psdisplay("Responding: "));

         // Maybe we do not respond?
         if (resp.status == wb_cycle_resp::NO_RESP ) do_break=1;

         end //do_break
         if(!do_break) begin
 
         // Insert the required number of wait states
         // less what has already been inserted because
         // of the response delay
         if (n_wss > resp.n_wss) begin
            `vmm_warning(this.log, $psprintf("Number of requested wait state in response (%0d) already exhausted due to delay in responding (%0d)",
                                             resp.n_wss, n_wss));
         end
         else begin
            repeat (resp.n_wss - n_wss) begin
               @ (this.sigs.sck);
            end
         end

         // Complete the cycle
         if (req.kind == wb_cycle::READ ) begin
            this.sigs.rdat <= resp.data;
            this.sigs.rtgd <= resp.tag;
         end

         case (resp.status)
            wb_cycle_resp::ACK : this.sigs.ack <= 1'b1;
            wb_cycle_resp::RTY : this.sigs.rty <= 1'b1;
            wb_cycle_resp::ERR : this.sigs.err <= 1'b1;
         endcase

         // Wait for the end of the cycle or back-to-back cycles

         // Make sure the write data that was latched is the one we sampled
         if (req.kind == wb_cycle::WRITE ) begin
            bit [63:0] dat;
            bit [15:0] tag;

            @ (this.sigs.sck);

            dat = this.sigs.sck.wdat;
            if (dat !== req.data)
               `vmm_error(this.log, $psprintf("DAT_I not stable during write cycle: %h vs %h", this.sigs.sck.wdat, req.data));
            tag = this.sigs.sck.wtgd;
            if (tag !== req.tgd)
               `vmm_error(this.log, $psprintf("TGD_I not stable during write cycle: %h vs %h", this.sigs.sck.wtgd, req.tgd));
         end

         `vmm_callback(wb_slave_callbacks,
                       post_cycle(this, resp));

         end //do_break
      end // anonymous begin
     end //do_continue
   end // while
endtask: main
   

//
// wb_ram
//

function wb_ram::new(string                inst,
                     int unsigned          stream_id = -1,
                     wb_cycle_channel      req_chan = null,
                     wb_cycle_resp_channel resp_chan = null,
                     wb_cycle_resp         resp_factory = null);
   super.new("Wishbone RAM", inst, stream_id);

   if (req_chan == null) req_chan = new("Wishbone RAM Request Channel",
                                        inst);
   this.req_chan = req_chan;

   if (resp_chan == null) resp_chan = new("Wishbone RAM Response Channel",
                                          inst);
   this.resp_chan = resp_chan;

   if (resp_factory == null) resp_factory = new(null, null);
   this.resp_factory = resp_factory;
endfunction: new
  

function void wb_ram::reset_xactor(reset_e rst_typ = SOFT_RST);
   super.reset_xactor(rst_typ);
endfunction: reset_xactor

   
task wb_ram::main();
   fork
      super.main();
   join

   forever begin
      wb_cycle req;
      wb_cycle_resp resp;

      this.wait_if_stopped_or_empty(this.req_chan);
      this.req_chan.get(req);

      `vmm_trace(this.log, req.psdisplay("Request: "));

      $cast(resp, this.resp_factory.copy());
      resp.req = req;
      resp.data.rand_mode(0);
      resp.status = wb_cycle_resp::ACK ;
      resp.status.rand_mode(0);

      // Implement a RAM behavior
      if (req.kind == wb_cycle::READ ) resp.data = this.read(req.addr);

      `vmm_callback(wb_ram_callbacks,
                    pre_response(this, req, resp));

      if (req.kind == wb_cycle::WRITE ) this.write(req.addr, req.data);
      
      `vmm_trace(this.log, resp.psdisplay("Responding: "));

      this.resp_chan.put(resp);
   end
endtask: main

   
function bit [63:0] wb_ram::read(bit [63:0] addr);
   read = (this.ram.exists(addr)) ? this.ram[addr] : 64'bx;
endfunction: read

   
function void wb_ram::write(bit [63:0] addr,
                            bit [63:0] data);
   this.ram[addr] = data;
endfunction: write
