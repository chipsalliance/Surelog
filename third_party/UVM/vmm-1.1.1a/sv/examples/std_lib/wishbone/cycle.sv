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


// Example 4-29
// Example 4-31   
class wb_cycle extends vmm_data;

   static vmm_log log = new("wb_cycle", "class");

   wb_cfg cfg;  // Must be non-NULL to randomize

   typedef enum {READ, WRITE, BLK_RD, BLK_WR, RMW} cycle_kinds_e;
   rand cycle_kinds_e kind;

   typedef enum {CLASSIC, CONSTANT,
                 LINEAR, WRAP4, WRAP8, WRAP16,
                 EOB} pipelining_e;
   rand pipelining_e next_cycle;

   rand bit [63:0] addr;
   rand bit [63:0] data;
   rand bit [ 7:0] sel;
   rand bit [15:0] tgc;
   rand bit [15:0] tga;
   rand bit [15:0] tgd;
   rand bit        lock;

   int n_wss;

   typedef enum {UNKNOWN, ACK, RTY, ERR, TIMEOUT} status_e;
   status_e status;
  

   constraint wb_cycle_valid {
      if (cfg.cycles == wb_cfg::CLASSIC ) next_cycle == CLASSIC;
   }

   constraint supported {
      next_cycle == CLASSIC;
      kind == READ || kind == WRITE;
   }

   constraint valid_address {
      if (cfg.port_size - cfg.granularity == 1) addr[0:0] == 1'b0;
      if (cfg.port_size - cfg.granularity == 2) addr[1:0] == 2'b00;
      if (cfg.port_size - cfg.granularity == 3) addr[2:0] == 3'b000;
   }

   constraint valid_sel {
      sel inside {8'h01, 8'h03, 8'h07, 8'h0F, 8'h1F, 8'h3F, 8'h7F, 8'hFF};
      if (cfg.port_size - cfg.granularity == 0) sel[7:1] == 7'h00;
      if (cfg.port_size - cfg.granularity == 1) sel[7:2] == 6'h00;
      if (cfg.port_size - cfg.granularity == 2) sel[7:4] == 4'h0;
   }

   constraint tc1;
   constraint tc2;
   constraint tc3;
  

   extern function new(wb_cfg cfg = null);

   extern function void pre_randomize();

   extern virtual function vmm_data allocate();
   extern virtual function vmm_data copy(vmm_data to = null);

   extern virtual function bit compare(vmm_data      to,
                                       output string diff,
                                       input int     kind = -1);

   extern virtual function string psdisplay(string prefix = "");

   extern virtual function bit is_valid(bit silent = 1,
                                        int kind   = -1);
endclass: wb_cycle


// Example 4-31   
`vmm_channel(wb_cycle)
`vmm_atomic_gen(wb_cycle, "Wishbone Cycle Descriptor")
`vmm_scenario_gen(wb_cycle, "Wishbone Cycle Descriptor")


class wb_cycle_resp extends vmm_data;

   static vmm_log log = new("wb_cycle_resp", "class");

   wb_cycle req;      // Must be non-NULL to randomize
   wb_slave_cfg cfg;  // Must be non-NULL to randomize

   rand bit [63:0] data;
   rand bit [15:0] tag;

   rand int n_wss;

   typedef enum {ACK, RTY, ERR, NO_RESP} status_e;
   rand status_e status;

   constraint valid_n_wss {
      n_wss <= cfg.max_n_wss;
      n_wss >= 0;
   }

   constraint targetted_device {
      if (cfg.min_addr <= req.addr && req.addr <= cfg.max_addr) status != NO_RESP;
      else status == NO_RESP;
   }

   constraint tc1;
   constraint tc2;
   constraint tc3;


   extern function new(wb_cycle     req,
                       wb_slave_cfg cfg);

   extern function void pre_randomize();

   extern virtual function vmm_data allocate();
   extern virtual function vmm_data copy(vmm_data to = null);

   extern virtual function bit compare(vmm_data      to,
                                       output string diff,
                                       input int     kind = -1);

   extern virtual function string psdisplay(string prefix = "");
      
   extern virtual function bit is_valid(bit silent = 1,
                                        int kind   = -1);
endclass: wb_cycle_resp

`vmm_channel(wb_cycle_resp)



//
// wb_cycle
//

function wb_cycle::new(wb_cfg cfg=null);
   super.new(this.log);
   this.cfg = cfg;
endfunction: new

function void wb_cycle::pre_randomize();
   if (this.cfg == null) begin
      `vmm_error(this.log, "NULL 'cfg' property in randomized instance");
   end
endfunction: pre_randomize


function vmm_data wb_cycle::allocate();
   wb_cycle tr = new;
   allocate = tr;
endfunction: allocate 


function vmm_data wb_cycle::copy(vmm_data to=null);
   wb_cycle tr;

   if (to == null) tr = new(this.cfg);
   else if (!$cast(tr, to)) begin
      `vmm_fatal(this.log, "Unable to copy to non-wb_cycle instance");
      return null;
   end

   this.copy_data(tr);

   tr.cfg = this.cfg;

   tr.kind       = this.kind;
   tr.next_cycle = this.next_cycle;
   tr.addr       = this.addr;
   tr.data       = this.data;
   tr.sel        = this.sel;
   tr.tgc        = this.tgc;
   tr.tga        = this.tga;
   tr.tgd        = this.tgd;
   tr.lock       = this.lock;
   tr.status     = this.status;

   copy = tr;
endfunction: copy


function bit wb_cycle::compare(vmm_data      to,
                               output string diff,
                               input int     kind = -1);
   wb_cycle tr;

   compare = 0;

   if (to == null) begin
      `vmm_fatal(this.log, "Cannot compare to null instance");
      diff = "Comparing to null instance";
      return 0;
   end
   else if (!$cast(tr, to)) begin
      `vmm_fatal(this.log, "Unable to compare to non-wb_cycle instance");
      diff = "Comparing to non-wb_cycle instance";
      return 0;
   end

   if (this.kind !== tr.kind) begin
      $sformat(diff, "kind %0s !== %0s", this.kind.name(), tr.kind.name());
      return 0;
   end

   if (this.next_cycle !== tr.next_cycle) begin
      $sformat(diff, "next_cycle %0s !== %0s", this.next_cycle.name(), tr.next_cycle.name());
      return 0;
   end

   if (this.addr !== tr.addr) begin
      $sformat(diff, "addr 64'h%h !== 64'h%h", this.addr, tr.addr);
      return 0;
   end

   if (this.data !== tr.data) begin
      $sformat(diff, "data 64'%h !== 64'h%h", this.data, tr.data);
      return 0;
   end

   if (this.sel !== tr.sel) begin
      $sformat(diff, "sel 8'%h !== 8'%h", this.sel, tr.sel);
      return 0;
   end

   if (this.tgc !== tr.tgc) begin
      $sformat(diff, "tgc 16'h%h !== 16'h%h", this.tgc, tr.tgc);
      return 0;
   end

   if (this.tga !== tr.tga) begin
      $sformat(diff, "tga 16'h%h !== 16'h%h", this.tga, tr.tga);
      return 0;
   end

   if (this.tgd !== tr.tgd) begin
      $sformat(diff, "tgd 16'h%h !== 16'h%h", this.tgd, tr.tgd);
      return 0;
   end

   if (this.lock !== tr.lock) begin
      $sformat(diff, "lock 'b%b !== 'b%b", this.lock, tr.lock);
      return 0;
   end

   if (this.status !== tr.status) begin
      $sformat(diff, "status %0s !== %0s", this.status.name(), tr.status.name());
      return 0;
   end

   compare = 1;
endfunction: compare


function string wb_cycle::psdisplay(string prefix = "");
   $sformat(psdisplay, "%0sWishbone %0socked %0s %0s Cycle #%0d.%0d.%0d\n", prefix,
            (this.lock) ? "L" : "Unl", this.kind.name(), this.next_cycle.name(),
            this.stream_id, this.scenario_id, this.data_id);
   $sformat(psdisplay, "%0s%0s   Addr=64'h%h, Data=64'h%h, Sel=8'h%h\n",
            psdisplay, prefix, this.addr, this.data, this.sel);
   $sformat(psdisplay, "%0s%0s   Tags: C=16'h%h, A=16'h%h, D=16'h%h. Status=%0s",
            psdisplay, prefix, this.tgc, this.tga, this.tgd, this.status.name());
endfunction: psdisplay
  

function bit wb_cycle::is_valid(bit silent = 1,
                                int kind = -1);
`ifdef NO_RANDOMIZE_NULL
   is_valid = 1;
`else
   is_valid = this.randomize(null);
`endif
endfunction: is_valid



  //
  // wb_cycle_resp
  //

function wb_cycle_resp::new(wb_cycle     req,
                            wb_slave_cfg cfg);
   super.new(this.log);
   this.req = req;
   this.cfg = cfg;

   if (req != null) begin
      this.stream_id   = this.req.stream_id;
      this.scenario_id = this.req.scenario_id;
      this.data_id     = this.req.data_id;
   end
endfunction: new

function void wb_cycle_resp::pre_randomize();
   if (this.req == null) begin
      `vmm_fatal(this.log, "NULL 'req' property in randomized instance");
   end
   if (this.cfg == null) begin
      `vmm_fatal(this.log, "NULL 'cfg' property in randomized instance");
   end
endfunction: pre_randomize


function vmm_data wb_cycle_resp::allocate();
   wb_cycle_resp tr = new(this.req, this.cfg);
   allocate = tr;
endfunction: allocate 


function vmm_data wb_cycle_resp::copy(vmm_data to = null);
   wb_cycle_resp tr;

   if (to == null) tr = new(this.req, this.cfg);
   else if (!$cast(tr, to)) begin
      `vmm_fatal(this.log, "Unable to copy to non-wb_cycle_resp instance");
      return null;
   end

   this.copy_data(tr);

   tr.req = this.req;
   tr.cfg = this.cfg;

   tr.data   = this.data;
   tr.tag    = this.tag;
   tr.n_wss  = this.n_wss;
   tr.status = this.status;

   copy = tr;
endfunction: copy


function bit wb_cycle_resp::compare(vmm_data      to,
                                    output string diff,
                                    input int     kind = -1);
   wb_cycle_resp tr;

   compare = 0;

   if (to == null) begin
      `vmm_fatal(this.log, "Cannot compare to null instance");
      diff = "Comparing to null instance";
      return 0;
   end
   else if (!$cast(tr, to)) begin
      `vmm_fatal(this.log, "Unable to compare to non-wb_cycle instance");
      diff = "Comparing to non-wb_cycle_resp instance";
      return 0;
   end

   if (this.data !== tr.data) begin
      $sformat(diff, "data 64'%h !== 64'h%h", this.data, tr.data);
      return 0;
   end

   if (this.tag !== tr.tag) begin
      $sformat(diff, "tag 16'h%h !== 16'h%h", this.tag, tr.tag);
      return 0;
   end

   if (this.n_wss !== tr.n_wss) begin
      $sformat(diff, "n_wss %0d !== %0d", this.n_wss, tr.n_wss);
      return 0;
   end

   if (this.status !== tr.status) begin
      $sformat(diff, "status %0s !== %0s", this.status.name(), tr.status.name());
      return 0;
   end

   compare = 1;
endfunction: compare


function string wb_cycle_resp::psdisplay(string prefix = "");
   $sformat(psdisplay, "%0sResponse #%0d.%0d.%0d", prefix,
            this.stream_id, this.scenario_id, this.data_id);
   $sformat(psdisplay, "%0s\n%0s", psdisplay, this.req.psdisplay({prefix, "   to: "}));
   if (this.req.kind == wb_cycle::READ ) begin
      $sformat(psdisplay, "%0s\n%0s   Data=64'h%h, Tag=16'h%h",
               psdisplay, prefix, this.data, this.tag);
   end
   $sformat(psdisplay, "%0s\n%0s   Status=%0s after %0d WSS",
            psdisplay, prefix, this.status.name(), this.n_wss);
endfunction: psdisplay

   
function bit wb_cycle_resp::is_valid(bit silent = 1,
                                     int kind = -1);
`ifdef NO_RANDOMIZE_NULL
   is_valid = 1;
`else
   is_valid = this.randomize(null);
`endif
endfunction: is_valid
