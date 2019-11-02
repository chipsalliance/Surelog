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


`ifndef RVM_RW__SV
`define RVM_RW__SV

`include "vmm.sv"

`ifndef VMM_RW_ADDR_WIDTH
  `ifdef VMM_RAL_ADDR_WIDTH
    `define VMM_RW_ADDR_WIDTH `VMM_RAL_ADDR_WIDTH
  `else
    `define VMM_RW_ADDR_WIDTH 64
  `endif
`endif
`ifndef VMM_RW_DATA_WIDTH
  `ifdef VMM_RAL_DATA_WIDTH
    `define VMM_RW_DATA_WIDTH `VMM_RAL_DATA_WIDTH
  `else
    `define VMM_RW_DATA_WIDTH 64
  `endif
`endif


class vmm_rw;
   typedef enum {
      READ,
      WRITE,
      EXPECT
   } kind_e;

   typedef enum {
      IS_OK,
      ERROR,
      RETRY,
      TIMEOUT,
`ifdef VMM_RAL_PIPELINED_ACCESS
      PENDING,
`endif
      HAS_X
   } status_e;
endclass: vmm_rw


class vmm_rw_access extends `VMM_DATA;
   static vmm_log log = new("vmm_rw_access", "class");

   rand vmm_rw::kind_e kind;

   rand bit   [`VMM_RW_ADDR_WIDTH-1:0] addr;
   rand logic [`VMM_RW_DATA_WIDTH-1:0] data;
   rand int                            n_bits = `VMM_RW_DATA_WIDTH;

   vmm_rw::status_e status;

   constraint valid_vmm_rw_access {
      n_bits > 0;
      n_bits < `VMM_RW_DATA_WIDTH;
   }

   extern function new();
   extern virtual function string psdisplay(string prefix = "");
endclass: vmm_rw_access
`vmm_channel(vmm_rw_access)


class vmm_rw_burst extends vmm_rw_access;
   rand int unsigned n_beats;
   rand bit   [`VMM_RW_ADDR_WIDTH-1:0] incr_addr;
   rand bit   [`VMM_RW_ADDR_WIDTH-1:0] max_addr;
   rand logic [`VMM_RW_DATA_WIDTH-1:0] data[];
        vmm_data                       user_data;

   constraint vmm_rw_burst_valid {
      n_beats > 0;
      max_addr >= addr;
      if (kind == vmm_rw::WRITE || kind == vmm_rw::EXPECT) data.size() == n_beats;
      else data.size() == 0;
   }

   constraint reasonable {
      n_beats <= 1024;
      incr_addr inside {0, 1, 2, 4, 8, 16, 32};
   }

   constraint linear {
      incr_addr == 1;
      max_addr == addr + n_beats - 1;
   }

   constraint fifo {
      incr_addr == 0;
      max_addr == addr;
   }

   constraint wrap {
      incr_addr > 0;
      max_addr < addr + (n_beats - 1)* incr_addr;
   }

   function new();
      this.linear.constraint_mode(0);
      this.fifo.constraint_mode(0);
      this.wrap.constraint_mode(0);
   endfunction: new
endclass: vmm_rw_burst


typedef class vmm_rw_xactor;
class vmm_rw_xactor_callbacks extends vmm_xactor_callbacks;
   virtual task pre_single(vmm_rw_xactor xactor,
                           vmm_rw_access tr);
   endtask

   virtual task pre_burst(vmm_rw_xactor xactor,
                          vmm_rw_burst  tr);
   endtask

   virtual task post_single(vmm_rw_xactor xactor,
                            vmm_rw_access tr);
   endtask

   virtual task post_burst(vmm_rw_xactor xactor,
                           vmm_rw_burst  tr);
   endtask
endclass: vmm_rw_xactor_callbacks


class vmm_rw_xactor extends `VMM_XACTOR;
   typedef enum {BURST_DONE = 99990,
                 SINGLE_DONE} notifications_e;

   vmm_rw_access_channel exec_chan;

   extern function new(string name,
                       string inst,
                       int    stream_id = -1,
                       vmm_rw_access_channel exec_chan = null);

   extern protected virtual task execute_single(vmm_rw_access tr);
   extern protected virtual task execute_burst(vmm_rw_burst tr);

   extern protected virtual task main();
   extern function void reset_xactor(vmm_xactor::reset_e rst_typ = SOFT_RST);
endclass: vmm_rw_xactor


function vmm_rw_access::new();
   super.new(this.log);
endfunction: new

function string vmm_rw_access::psdisplay(string prefix = "");
   string fmt;
   $sformat(fmt, "%0dh", this.n_bits);
   $sformat(psdisplay, {"%s%s @ 0x%h = %0d'h%", fmt, "\n"}, prefix,
            kind.name(), addr, n_bits, data);
endfunction: psdisplay


function vmm_rw_xactor::new(string                name,
                            string                inst,
                            int                   stream_id = -1,
                            vmm_rw_access_channel exec_chan = null);
   super.new(name, inst, stream_id);

   if (exec_chan == null) exec_chan = new({name, " Input Channel"}, inst);
   this.exec_chan = exec_chan;

   this.log.is_above(this.exec_chan.log);

   void'(this.notify.configure(BURST_DONE));
   void'(this.notify.configure(SINGLE_DONE));
endfunction: new


task vmm_rw_xactor::execute_single(vmm_rw_access tr);
   `vmm_fatal(this.log, "Undefined execute_single() method in vmm_rw_xactor extension");
endtask: execute_single


task vmm_rw_xactor::execute_burst(vmm_rw_burst tr);
   bit [`VMM_RW_ADDR_WIDTH-1:0] addr;
   int i;

   addr = tr.addr;
   i = 0;
   tr.status = vmm_rw::IS_OK;
   if (tr.kind == vmm_rw::READ) tr.data = new [tr.n_beats];
   repeat (tr.n_beats) begin
      vmm_rw_access s = new;
      s.kind = tr.kind;
      s.addr = addr;
      if (s.kind != vmm_rw::READ) s.data = tr.data[i++];
      this.execute_single(s);
      if (s.kind == vmm_rw::READ) tr.data[i++] = s.data;
      if (s.status != vmm_rw::IS_OK) begin
         tr.status = s.status;
         return;
      end

      addr += tr.incr_addr;
      if (addr > tr.max_addr) addr = addr - tr.max_addr + tr.addr;
   end
   tr.status = vmm_rw::IS_OK;
endtask: execute_burst


task vmm_rw_xactor::main();
   vmm_rw_access tr;
   vmm_rw_burst  br;

   fork
      super.main();
   join_none

   forever begin
      this.wait_if_stopped_or_empty(this.exec_chan);

`ifdef VMM_RAL_PIPELINED_ACCESS
      this.exec_chan.get(tr);
`else
      this.exec_chan.activate(tr);
      void'(this.exec_chan.start());
`endif

      if ($cast(br, tr)) begin
         `vmm_callback(vmm_rw_xactor_callbacks,
                       pre_burst(this, br));
         this.execute_burst(br);
         `vmm_callback(vmm_rw_xactor_callbacks,
                       post_burst(this, br));
         this.notify.indicate(BURST_DONE, br);
      end
      else begin
         `vmm_callback(vmm_rw_xactor_callbacks, pre_single(this, tr));
         this.execute_single(tr);
`ifdef VMM_RAL_PIPELINED_ACCESS
         if (tr.status == vmm_rw::PENDING) begin
            fork
               vmm_rw_access rw = tr;
               begin
                  rw.notify.wait_for(vmm_data::ENDED);
                  `vmm_callback(vmm_rw_xactor_callbacks,
                                post_single(this, rw));
                  this.notify.indicate(SINGLE_DONE, rw);
               end
            join_none
         end
`else
         `vmm_callback(vmm_rw_xactor_callbacks,
                       post_single(this, tr));
         this.notify.indicate(SINGLE_DONE, tr);
`endif
      end

`ifndef VMM_RAL_PIPELINED_ACCESS
      void'(this.exec_chan.complete());
      void'(this.exec_chan.remove());
`endif
   end
endtask: main


function void vmm_rw_xactor::reset_xactor(vmm_xactor::reset_e rst_typ= SOFT_RST);
   vmm_rw_access tr;

   super.reset_xactor(rst_typ);

   // Force a completion of the transaction to avoid
   // leaving the RAL model blocked
   tr = this.exec_chan.active_slot();
   if (tr != null) begin
      tr.status = vmm_rw::RETRY;
      void'(this.exec_chan.complete());
      void'(this.exec_chan.remove());
   end
   this.exec_chan.flush();
endfunction: reset_xactor

`endif // RVM_RW__SV
