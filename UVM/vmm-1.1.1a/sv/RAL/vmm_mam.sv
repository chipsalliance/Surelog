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


`ifndef VMM_MAM__SV
`define VMM_MAM__SV


typedef class vmm_mam_cfg;
typedef class vmm_mam;

typedef class vmm_ral_mem;
typedef class vmm_ral_mem_burst;


class vmm_mam_region;
   /*local*/ bit [63:0] Xstart_offsetX;  // Can't be local since function
   /*local*/ bit [63:0] Xend_offsetX;    // calls not supported in constraints

   local int unsigned len;
   local int unsigned n_bytes;
   local vmm_mam      parent;

   /*local*/ vmm_ral_vreg XvregX;

   extern /*local*/ function new(bit [63:0]   start_offset,
                                 bit [63:0]   end_offset,
                                 int unsigned len,
                                 int unsigned n_bytes,
                                 vmm_mam      parent);

   extern function bit [63:0] get_start_offset();
   extern function bit [63:0] get_end_offset();

   extern function int unsigned get_len();
   extern function int unsigned get_n_bytes();

   extern function string psdisplay(string prefix = "");

   extern function void release_region();

   extern function vmm_ral_mem get_memory();
   extern function vmm_ral_vreg get_virtual_registers();

   extern task write(output vmm_rw::status_e              status,
                     input  bit [`VMM_RAL_ADDR_WIDTH-1:0] offset,
                     input  bit [`VMM_RAL_DATA_WIDTH-1:0] value,
                     input  vmm_ral::path_e               path   = vmm_ral::DEFAULT,
                     input  string                        domain = "",
                     input  int                           data_id = -1,
                     input  int                           scenario_id = -1,
                     input  int                           stream_id = -1);

   extern task read(output vmm_rw::status_e              status,
                    input  bit [`VMM_RAL_ADDR_WIDTH-1:0] offset,
                    output bit [`VMM_RAL_DATA_WIDTH-1:0] value,
                    input  vmm_ral::path_e               path   = vmm_ral::DEFAULT,
                    input  string                        domain = "",
                    input  int                           data_id = -1,
                    input  int                           scenario_id = -1,
                    input  int                           stream_id = -1);

   extern task burst_write(output vmm_rw::status_e              status,
                           input  vmm_ral_mem_burst             burst,
                           input  bit [`VMM_RAL_DATA_WIDTH-1:0] value[],
                           input  vmm_ral::path_e               path   = vmm_ral::DEFAULT,
                           input  string                        domain = "",
                           input  int                           data_id = -1,
                           input  int                           scenario_id = -1,
                           input  int                           stream_id = -1);

   extern task burst_read(output vmm_rw::status_e              status,
                          input  vmm_ral_mem_burst             burst,
                          output bit [`VMM_RAL_DATA_WIDTH-1:0] value[],
                          input  vmm_ral::path_e               path   = vmm_ral::DEFAULT,
                          input  string                        domain = "",
                          input  int                           data_id = -1,
                          input  int                           scenario_id = -1,
                          input  int                           stream_id = -1);

   extern task poke(output vmm_rw::status_e              status,
                    input  bit [`VMM_RAL_ADDR_WIDTH-1:0] offset,
                    input  bit [`VMM_RAL_DATA_WIDTH-1:0] value,
                    input  int                           data_id = -1,
                    input  int                           scenario_id = -1,
                    input  int                           stream_id = -1);

   extern task peek(output vmm_rw::status_e              status,
                    input  bit [`VMM_RAL_ADDR_WIDTH-1:0] offset,
                    output bit [`VMM_RAL_DATA_WIDTH-1:0] value,
                    input  int                           data_id = -1,
                    input  int                           scenario_id = -1,
                    input  int                           stream_id = -1);
endclass


class vmm_mam_allocator;
   int unsigned len;

   rand bit [63:0] start_offset;

   bit [63:0] min_offset;
   bit [63:0] max_offset;

   vmm_mam_region in_use[$];

   constraint vmam_mam_allocator_valid {
      start_offset >= min_offset;
      start_offset <= max_offset - len + 1;
   }

   constraint vmam_mam_allocator_no_overlap {
      foreach (in_use[i]) {
         !(start_offset <= in_use[i].Xend_offsetX &&
           start_offset + len - 1 >= in_use[i].Xstart_offsetX);
      }
   }

endclass


class vmm_mam;

   typedef enum {GREEDY, THRIFTY} alloc_mode_e;
   typedef enum {BROAD, NEARBY}   locality_e;

   vmm_log log;

   local vmm_mam_cfg cfg;

   vmm_mam_allocator default_alloc;
   local vmm_ral_mem memory;

   local vmm_mam_region in_use[$];
   local int for_each_idx = -1;

   extern function new(string      name,
                       vmm_mam_cfg cfg,
                       vmm_ral_mem mem=null);

   extern function vmm_mam_cfg reconfigure(vmm_mam_cfg cfg = null);

   extern function vmm_mam_region reserve_region(bit [63:0]   start_offset,
                                                 int unsigned n_bytes);
   extern function vmm_mam_region request_region(int unsigned n_bytes,
                                                 vmm_mam_allocator alloc = null);
   extern function void release_region(vmm_mam_region region);
   extern function void release_all_regions();


   extern function string psdisplay(string prefix = "");
   extern function vmm_mam_region for_each(bit reset = 0);
   extern function vmm_ral_mem get_memory();

endclass: vmm_mam


class vmm_mam_cfg;
   rand int unsigned n_bytes;

   rand bit [63:0] start_offset;
   rand bit [63:0] end_offset;

   rand vmm_mam::alloc_mode_e mode;
   rand vmm_mam::locality_e   locality;

   constraint vmm_mam_cfg_valid {
      end_offset > start_offset;
      n_bytes < 64;
   }
endclass



//------------------------------------------------------------------
//
//  Implementation
//

function vmm_mam_region::new(bit [63:0] start_offset,
                             bit [63:0] end_offset,
                             int unsigned len,
                             int unsigned n_bytes,
                             vmm_mam      parent);
   this.Xstart_offsetX = start_offset;
   this.Xend_offsetX   = end_offset;
   this.len            = len;
   this.n_bytes        = n_bytes;
   this.parent         = parent;
   this.XvregX         = null;
endfunction: new


function bit [63:0] vmm_mam_region::get_start_offset();
   return this.Xstart_offsetX;
endfunction: get_start_offset


function bit [63:0] vmm_mam_region::get_end_offset();
   return this.Xend_offsetX;
endfunction: get_end_offset


function int unsigned vmm_mam_region::get_len();
   return this.len;
endfunction: get_len


function int unsigned vmm_mam_region::get_n_bytes();
   return this.n_bytes;
endfunction: get_n_bytes


function string vmm_mam_region::psdisplay(string prefix = "");
   $sformat(psdisplay, "%s['h%h:'h%h]", prefix,
            this.Xstart_offsetX, this.Xend_offsetX);
endfunction: psdisplay


function void vmm_mam_region::release_region();
   this.parent.release_region(this);
endfunction


function vmm_ral_mem vmm_mam_region::get_memory();
   return this.parent.get_memory();
endfunction: get_memory


function vmm_ral_vreg vmm_mam_region::get_virtual_registers();
   return this.XvregX;
endfunction: get_virtual_registers


function vmm_mam::new(string      name,
                      vmm_mam_cfg cfg,
                      vmm_ral_mem mem = null);
   this.log           = new("Memory Allocation Manager", name);
   this.cfg           = cfg;
   this.memory        = mem;
   this.default_alloc = new;
endfunction: new


function vmm_mam_cfg vmm_mam::reconfigure(vmm_mam_cfg cfg = null);
   if (cfg == null) return this.cfg;

   // Cannot reconfigure n_bytes
   if (cfg.n_bytes !== this.cfg.n_bytes) begin
      `vmm_error(this.log,
                 $psprintf("Cannot reconfigure Memory Allocation Manager with a different number of bytes (%0d !== %0d)",
                           cfg.n_bytes, this.cfg.n_bytes));
      return this.cfg;
   end

   // All currently allocated regions must fall within the new space
   `foreach (this.in_use,i) begin
      if (this.in_use[i].get_start_offset() < cfg.start_offset ||
          this.in_use[i].get_end_offset() > cfg.end_offset) begin
         `vmm_error(this.log,
                    $psprintf("Cannot reconfigure Memory Allocation Manager with a currently allocated region outside of the managed address range ([%0d:%0d] outside of [%0d:%0d])",
                              this.in_use[i].get_start_offset(),
                              this.in_use[i].get_end_offset(),
                              cfg.start_offset, cfg.end_offset));
         return this.cfg;
      end
   end

   reconfigure = this.cfg;
   this.cfg = cfg;
endfunction: reconfigure


function vmm_mam_region vmm_mam::reserve_region(bit [63:0]   start_offset,
                                                int unsigned n_bytes);
   bit [63:0] end_offset;

   if (n_bytes == 0) begin
      `vmm_error(this.log, "Cannot reserve 0 bytes");
      return null;
   end

   if (start_offset < this.cfg.start_offset) begin
      `vmm_error(this.log, $psprintf("Cannot reserve before start of memory space: 'h%h < 'h%h",
                                     start_offset, this.cfg.start_offset));
      return null;
   end

   end_offset = start_offset + ((n_bytes-1) / this.cfg.n_bytes);
   n_bytes = (end_offset - start_offset + 1) * this.cfg.n_bytes;

   if (end_offset > this.cfg.end_offset) begin
      `vmm_error(this.log, $psprintf("Cannot reserve past end of memory space: 'h%h > 'h%h",
                                     end_offset, this.cfg.end_offset));
      return null;
   end

   `vmm_trace(this.log, $psprintf("Attempting to reserve ['h%h:'h%h]...",
                                  start_offset, end_offset));

   `foreach (this.in_use,i) begin
      if (start_offset <= this.in_use[i].get_end_offset() &&
          end_offset >= this.in_use[i].get_start_offset()) begin
         // Overlap!
         `vmm_error(this.log, $psprintf("Cannot reserve ['h%h:'h%h] because it overlaps with %s",
                                        start_offset, end_offset,
                                        this.in_use[i].psdisplay()));
         return null;
      end

      // Regions are stored in increasing start offset
      if (start_offset > this.in_use[i].get_start_offset()) begin
         reserve_region = new(start_offset, end_offset,
                              end_offset - start_offset + 1, n_bytes, this);
         this.in_use.insert(i, reserve_region);
         return reserve_region;
      end
   end

   reserve_region = new(start_offset, end_offset,
                        end_offset - start_offset + 1, n_bytes, this);
   this.in_use.push_back(reserve_region);
endfunction: reserve_region


function vmm_mam_region vmm_mam::request_region(int unsigned n_bytes,
                                                vmm_mam_allocator alloc = null);
   if (alloc == null) alloc = this.default_alloc;

   alloc.len        = (n_bytes-1) / this.cfg.n_bytes + 1;
   alloc.min_offset = this.cfg.start_offset;
   alloc.max_offset = this.cfg.end_offset;
   alloc.in_use     = this.in_use;

   if (!alloc.randomize()) begin
      `vmm_error(this.log, "Unable to randomize allocator");
      return null;
   end

   return reserve_region(alloc.start_offset, n_bytes);
endfunction: request_region


function void vmm_mam::release_region(vmm_mam_region region);

   if (region == null) return;

   `foreach (this.in_use,i) begin
      if (this.in_use[i] == region) begin
         this.in_use.delete(i);
         return;
      end
   end
   `vmm_error(this.log, region.psdisplay("Attempting to release unallocated region "));
endfunction: release_region


function void vmm_mam::release_all_regions();
`ifdef VCS2006_06
   // Work-around for NYI feature in VCS2006.06
   // but IEEE 1800-2009 compliant
   this.in_use.delete();
`else
`ifdef INCA
   this.in_use.delete();
`else
   // Works in VCS2008.03 or later
   // IEEE 1800-2005 compliant
   this.in_use = '{};
`endif
`endif
endfunction: release_all_regions


function string vmm_mam::psdisplay(string prefix = "");
   $sformat(psdisplay, "%sAllocated memory regions:\n", prefix);
   `foreach (this.in_use,i) begin
      $sformat(psdisplay, "%s%s   %s\n", psdisplay, prefix,
               this.in_use[i].psdisplay());
   end
endfunction: psdisplay


function vmm_mam_region vmm_mam::for_each(bit reset = 0);
   if (reset) this.for_each_idx = -1;

   this.for_each_idx++;

   if (this.for_each_idx >= this.in_use.size()) begin
      return null;
   end

   return this.in_use[this.for_each_idx];
endfunction: for_each


function vmm_ral_mem vmm_mam::get_memory();
   return this.memory;
endfunction: get_memory


task vmm_mam_region::write(output vmm_rw::status_e              status,
                           input  bit [`VMM_RAL_ADDR_WIDTH-1:0] offset,
                           input  bit [`VMM_RAL_DATA_WIDTH-1:0] value,
                           input  vmm_ral::path_e               path = vmm_ral::DEFAULT,
                           input  string                        domain = "",
                           input  int                           data_id = -1,
                           input  int                           scenario_id = -1,
                           input  int                           stream_id = -1);

   vmm_ral_mem mem = this.parent.get_memory();

   if (mem == null) begin
      `vmm_error(this.parent.log, "Cannot use vmm_mam_region::write() on a region that was allocated by a Memory Allocation Manager that was not associated with a vmm_ral_mem instance");
      status = vmm_rw::ERROR;
      return;
   end

   if (offset > this.len) begin
      `vmm_error(this.parent.log,
                 $psprintf("Attempting to write to an offset outside of the allocated region (%0d > %0d)",
                           offset, this.len));
      status = vmm_rw::ERROR;
      return;
   end

   mem.write(status, offset + this.get_start_offset(), value,
            path, domain,
            data_id, scenario_id, stream_id);
endtask: write


task vmm_mam_region::read(output vmm_rw::status_e              status,
                          input  bit [`VMM_RAL_ADDR_WIDTH-1:0] offset,
                          output bit [`VMM_RAL_DATA_WIDTH-1:0] value,
                          input  vmm_ral::path_e               path = vmm_ral::DEFAULT,
                          input  string                        domain = "",
                          input  int                           data_id = -1,
                          input  int                           scenario_id = -1,
                          input  int                           stream_id = -1);
   vmm_ral_mem mem = this.parent.get_memory();

   if (mem == null) begin
      `vmm_error(this.parent.log, "Cannot use vmm_mam_region::read() on a region that was allocated by a Memory Allocation Manager that was not associated with a vmm_ral_mem instance");
      status = vmm_rw::ERROR;
      return;
   end

   if (offset > this.len) begin
      `vmm_error(this.parent.log,
                 $psprintf("Attempting to read from an offset outside of the allocated region (%0d > %0d)",
                           offset, this.len));
      status = vmm_rw::ERROR;
      return;
   end

   mem.read(status, offset + this.get_start_offset(), value,
            path, domain,
            data_id, scenario_id, stream_id);
endtask: read


task vmm_mam_region::burst_write(output vmm_rw::status_e              status,
                                 input  vmm_ral_mem_burst             burst,
                                 input  bit [`VMM_RAL_DATA_WIDTH-1:0] value[],
                                 input  vmm_ral::path_e               path = vmm_ral::DEFAULT,
                                 input  string                        domain = "",
                                 input  int                           data_id = -1,
                                 input  int                           scenario_id = -1,
                                 input  int                           stream_id =-1);
   vmm_ral_mem mem = this.parent.get_memory();

   if (mem == null) begin
      `vmm_error(this.parent.log, "Cannot use vmm_mam_region::burst_write() on a region that was allocated by a Memory Allocation Manager that was not associated with a vmm_ral_mem instance");
      status = vmm_rw::ERROR;
      return;
   end

   if (burst.start_offset > this.len ||
       burst.max_offset   > this.len) begin
      `vmm_error(this.parent.log,
                 $psprintf("Attempting to burst-write to an offset outside of the allocated region ([%0d:%0d] > %0d)",
                           burst.start_offset, burst.max_offset, this.len));
      status = vmm_rw::ERROR;
      return;
   end

   begin
      vmm_ral_mem_burst b = new burst;
      b.start_offset += this.get_start_offset();
      b.max_offset   += this.get_start_offset();

      mem.burst_write(status, b, value,
                      path, domain,
                      data_id, scenario_id, stream_id);
   end
endtask: burst_write


task vmm_mam_region::burst_read(output vmm_rw::status_e              status,
                                input  vmm_ral_mem_burst             burst,
                                output bit [`VMM_RAL_DATA_WIDTH-1:0] value[],
                                input  vmm_ral::path_e               path = vmm_ral::DEFAULT,
                                input  string                        domain = "",
                                input  int                           data_id = -1,
                                input  int                           scenario_id = -1,
                                input  int                           stream_id = -1);
   vmm_ral_mem mem = this.parent.get_memory();

   if (mem == null) begin
      `vmm_error(this.parent.log, "Cannot use vmm_mam_region::burst_read() on a region that was allocated by a Memory Allocation Manager that was not associated with a vmm_ral_mem instance");
      status = vmm_rw::ERROR;
      return;
   end

   if (burst.start_offset > this.len ||
       burst.max_offset   > this.len) begin
      `vmm_error(this.parent.log,
                 $psprintf("Attempting to burst-read from an offset outside of the allocated region ([%0d:%0d] > %0d)",
                           burst.start_offset, burst.max_offset, this.len));
      status = vmm_rw::ERROR;
      return;
   end

   begin
      vmm_ral_mem_burst b = new burst;
      b.start_offset += this.get_start_offset();
      b.max_offset   += this.get_start_offset();

      mem.burst_read(status, b, value,
                     path, domain,
                     data_id, scenario_id, stream_id);
   end
endtask: burst_read


task vmm_mam_region::poke(output vmm_rw::status_e              status,
                          input  bit [`VMM_RAL_ADDR_WIDTH-1:0] offset,
                          input  bit [`VMM_RAL_DATA_WIDTH-1:0] value,
                          input  int                           data_id = -1,
                          input  int                           scenario_id = -1,
                          input  int                           stream_id = -1);
   vmm_ral_mem mem = this.parent.get_memory();

   if (mem == null) begin
      `vmm_error(this.parent.log, "Cannot use vmm_mam_region::poke() on a region that was allocated by a Memory Allocation Manager that was not associated with a vmm_ral_mem instance");
      status = vmm_rw::ERROR;
      return;
   end

   if (offset > this.len) begin
      `vmm_error(this.parent.log,
                 $psprintf("Attempting to poke to an offset outside of the allocated region (%0d > %0d)",
                           offset, this.len));
      status = vmm_rw::ERROR;
      return;
   end

   mem.poke(status, offset + this.get_start_offset(), value,
            data_id, scenario_id, stream_id);
endtask: poke


task vmm_mam_region::peek(output vmm_rw::status_e              status,
                          input  bit [`VMM_RAL_ADDR_WIDTH-1:0] offset,
                          output bit [`VMM_RAL_DATA_WIDTH-1:0] value,
                          input  int                           data_id = -1,
                          input  int                           scenario_id = -1,
                          input  int                           stream_id = -1);
   vmm_ral_mem mem = this.parent.get_memory();

   if (mem == null) begin
      `vmm_error(this.parent.log, "Cannot use vmm_mam_region::peek() on a region that was allocated by a Memory Allocation Manager that was not associated with a vmm_ral_mem instance");
      status = vmm_rw::ERROR;
      return;
   end

   if (offset > this.len) begin
      `vmm_error(this.parent.log,
                 $psprintf("Attempting to peek from an offset outside of the allocated region (%0d > %0d)",
                           offset, this.len));
      status = vmm_rw::ERROR;
      return;
   end

   mem.peek(status, offset + this.get_start_offset(), value,
            data_id, scenario_id, stream_id);
endtask: peek


`endif  // VMM_MAM__SV
