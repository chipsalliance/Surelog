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


typedef class vmm_ral_vfield;
class vmm_ral_vfield_callbacks extends vmm_ral_callbacks;

   virtual task pre_write(vmm_ral_vfield                    field,
                          longint unsigned                  idx,
                          ref bit [`VMM_RAL_DATA_WIDTH-1:0] wdat,
                          ref vmm_ral::path_e               path,
                          ref string                        domain);
   endtask: pre_write

   virtual task post_write(vmm_ral_vfield                field,
                           longint unsigned              idx,
                           bit [`VMM_RAL_DATA_WIDTH-1:0] wdat,
                           vmm_ral::path_e               path,
                           string                        domain,
                           ref vmm_rw::status_e          status);
   endtask: post_write

   virtual task pre_read(vmm_ral_vfield        field,
                         longint unsigned      idx,
                         ref vmm_ral::path_e   path,
                         ref string            domain);
   endtask: pre_read

   virtual task post_read(vmm_ral_vfield                    field,
                          longint unsigned                  idx,
                          ref bit [`VMM_RAL_DATA_WIDTH-1:0] rdat,
                          vmm_ral::path_e                   path,
                          string                            domain,
                          ref vmm_rw::status_e              status);
   endtask: post_read
endclass: vmm_ral_vfield_callbacks


class vmm_ral_vfield;
   static vmm_log log = new("RAL", "virtual field");

   local string name;
   local vmm_ral_vreg parent;
   local int unsigned lsb;
   local int unsigned size;

   vmm_ral_vfield_callbacks XcbsX[$];

   extern /*local*/ function new(vmm_ral_vreg     parent,
                                 string           name,
                                 int unsigned     size,
                                 int unsigned     lsb_pos);

   extern virtual function string get_name();
   extern virtual function string get_fullname();
   extern virtual function vmm_ral_vreg get_register();
   extern virtual function int unsigned get_lsb_pos_in_register();
   extern virtual function int unsigned get_n_bits();

   extern virtual function vmm_ral::access_e get_access(string domain = "");

   extern virtual function void display(string prefix = "");
   extern virtual function string psdisplay(string prefix = "");

   extern virtual task write(input  longint unsigned              idx,
                             output vmm_rw::status_e              status,
                             input  bit [`VMM_RAL_DATA_WIDTH-1:0] value,
                             input  vmm_ral::path_e               path = vmm_ral::DEFAULT,
                             input  string                        domain = "",
                             input  int                           data_id = -1,
                             input  int                           scenario_id =- 1,
                             input  int                           stream_id = -1);
   extern virtual task read(input  longint unsigned             idx,
                            output vmm_rw::status_e             status,
                            output bit[`VMM_RAL_DATA_WIDTH-1:0] value,
                            input  vmm_ral::path_e              path = vmm_ral::DEFAULT,
                            input  string                       domain = "",
                            input  int                          data_id = -1,
                            input  int                          scenario_id = -1,
                            input  int                          stream_id = -1);
               
   extern virtual task poke(input  longint unsigned              idx,
                            output vmm_rw::status_e              status,
                            input  bit [`VMM_RAL_DATA_WIDTH-1:0] value,
                            input  int                           data_id = -1,
                            input  int                           scenario_id =- 1,
                            input  int                           stream_id = -1);
   extern virtual task peek(input  longint unsigned             idx,
                            output vmm_rw::status_e             status,
                            output bit[`VMM_RAL_DATA_WIDTH-1:0] value,
                            input  int                          data_id = -1,
                            input  int                          scenario_id = -1,
                            input  int                          stream_id = -1);
               
   extern function void prepend_callback(vmm_ral_vfield_callbacks cb);
   extern function void append_callback(vmm_ral_vfield_callbacks cb);
   extern function void unregister_callback(vmm_ral_vfield_callbacks cb);
endclass: vmm_ral_vfield


function vmm_ral_vfield::new(vmm_ral_vreg      parent,
                             string            name,
                             int unsigned      size,
                             int unsigned      lsb_pos);
   this.parent = parent;
   this.name   = name;

   if (size == 0) begin
      `vmm_error(this.log, $psprintf("Virtual field \"%s\" cannot have 0 bits", this.get_fullname()));
      size = 1;
   end
   if (size > `VMM_RAL_DATA_WIDTH) begin
      `vmm_error(this.log, $psprintf("Virtual field \"%s\" cannot have more than %0d bits",
                                     this.get_fullname(),
                                     `VMM_RAL_DATA_WIDTH));
      size = `VMM_RAL_DATA_WIDTH;
   end

   this.size   = size;
   this.lsb    = lsb_pos;

   this.parent.register_field(this);
endfunction: new


function string vmm_ral_vfield::get_name();
   get_name = this.name;
endfunction: get_name


function string vmm_ral_vfield::get_fullname();
   get_fullname = {this.parent.get_fullname(), ".", this.name};
endfunction: get_fullname


function vmm_ral_vreg vmm_ral_vfield::get_register();
   get_register = this.parent;
endfunction: get_register


function int unsigned vmm_ral_vfield::get_lsb_pos_in_register();
   get_lsb_pos_in_register = this.lsb;
endfunction: get_lsb_pos_in_register


function int unsigned vmm_ral_vfield::get_n_bits();
   get_n_bits = this.size;
endfunction: get_n_bits


function vmm_ral::access_e vmm_ral_vfield::get_access(string domain = "");
   if (this.parent.get_memory() == null) begin
      `vmm_error(this.log, $psprintf("Cannot call vmm_ral_vfield::get_rights() on unimplemented virtual field \"%s\"",
                                     this.get_fullname()));
      return vmm_ral::RW;
   end

   get_access = this.parent.get_access(domain);
endfunction: get_access


function void vmm_ral_vfield::display(string prefix = "");
   $write("%s\n", this.psdisplay(prefix));
endfunction: display


function string vmm_ral_vfield::psdisplay(string prefix = "");
   $sformat(psdisplay, {"%s%s[%0d-%0d]"}, prefix,
            this.get_name(),
            this.get_lsb_pos_in_register() + this.get_n_bits() - 1,
            this.get_lsb_pos_in_register());
endfunction: psdisplay


task vmm_ral_vfield::write(input  longint unsigned              idx,
                           output vmm_rw::status_e              status,
                           input  bit [`VMM_RAL_DATA_WIDTH-1:0] value,
                           input  vmm_ral::path_e               path = vmm_ral::DEFAULT,
                           input  string                        domain = "",
                           input  int                           data_id = -1,
                           input  int                           scenario_id = -1,
                           input  int                           stream_id = -1);
   bit [`VMM_RAL_DATA_WIDTH-1:0] tmp;
   bit [`VMM_RAL_DATA_WIDTH-1:0] segval;
   bit [`VMM_RAL_ADDR_WIDTH-1:0] segoff;
   vmm_rw::status_e st;

   int flsb, fmsb, rmwbits;
   int segsiz, segn;
   vmm_ral_mem    mem;
   vmm_ral::path_e rm_path;

   mem = this.parent.get_memory();
   if (mem == null) begin
      `vmm_error(this.log, $psprintf("Cannot call vmm_ral_vfield::write() on unimplemented virtual register \"%s\"",
                                     this.get_fullname()));
      status = vmm_rw::ERROR;
      return;
   end

   if (path == vmm_ral::DEFAULT) begin
      vmm_ral_block blk = this.parent.get_block();
      path = blk.get_default_access();
   end

   status = vmm_rw::IS_OK;

   this.parent.XatomicX(1);

   if (value >> this.size) begin
      `vmm_warning(log, $psprintf("Writing value 'h%h that is greater than field \"%s\" size (%0d bits)", value, this.get_fullname(), this.get_n_bits()));
      value &= value & ((1<<this.size)-1);
   end
   tmp = 0;

   `foreach (this.XcbsX,j) begin
      vmm_ral_vfield_callbacks cb;
      if (!$cast(cb, this.XcbsX[j])) continue;
      cb.pre_write(this, idx, value, path, domain);
   end

   segsiz = mem.get_n_bytes() * 8;
   flsb    = this.get_lsb_pos_in_register();
   segoff  = this.parent.get_offset_in_memory(idx) + (flsb / segsiz);

   // Favor backdoor read to frontdoor read for the RMW operation
   rm_path = vmm_ral::DEFAULT;
   if (mem.get_backdoor() != null) rm_path = vmm_ral::BACKDOOR;

   // Any bits on the LSB side we need to RMW?
   rmwbits = flsb % segsiz;

   // Total number of memory segment in this field
   segn = (rmwbits + this.get_n_bits() - 1) / segsiz + 1;

   if (rmwbits > 0) begin
      bit [`VMM_RAL_ADDR_WIDTH-1:0] segn;

      mem.read(st, segoff, tmp, rm_path, domain,
               data_id, scenario_id, stream_id);
      if (st != vmm_rw::IS_OK) begin
         `vmm_error(this.log,
                    $psprintf("Unable to read LSB bits in %s[%0d] to for RMW cycle on virtual field %s.",
                              mem.get_fullname(), segoff, this.get_fullname()));
         status = vmm_rw::ERROR;
         this.parent.XatomicX(0);
         return;
      end

      value = (value << rmwbits) | (tmp & ((1<<rmwbits)-1));
   end

   // Any bits on the MSB side we need to RMW?
   fmsb = rmwbits + this.get_n_bits() - 1;
   rmwbits = (fmsb+1) % segsiz;
   if (rmwbits > 0) begin
      if (segn > 0) begin
         mem.read(st, segoff + segn - 1, tmp, rm_path, domain,
                  data_id, scenario_id, stream_id);
         if (st != vmm_rw::IS_OK) begin
            `vmm_error(this.log,
                       $psprintf("Unable to read MSB bits in %s[%0d] to for RMW cycle on virtual field %s.",
                                 mem.get_fullname(), segoff+segn-1,
                                 this.get_fullname()));
            status = vmm_rw::ERROR;
            this.parent.XatomicX(0);
            return;
         end
      end
      value |= (tmp & ~((1<<rmwbits)-1)) << ((segn-1)*segsiz);
   end

   // Now write each of the segments
   tmp = value;
   repeat (segn) begin
      mem.write(st, segoff, tmp, path, domain,
               data_id, scenario_id, stream_id);
      if (st != vmm_rw::IS_OK) status = vmm_rw::ERROR;

      segoff++;
      tmp = tmp >> segsiz;
   end

   `foreach (this.XcbsX,j) begin
      vmm_ral_vfield_callbacks cb;
      if (!$cast(cb, this.XcbsX[j])) continue;
      cb.post_write(this, idx, value, path, domain, status);
   end

   this.parent.XatomicX(0);

   `vmm_trace(this.log, $psprintf("Wrote virtual field \"%s\"[%0d] via %s with: 'h%h",
                                  this.get_fullname(), idx,
                                  (path == vmm_ral::BFM) ? "frontdoor" : "backdoor",
                                  value));

endtask: write


task vmm_ral_vfield::read(input longint unsigned              idx,
                          output vmm_rw::status_e             status,
                          output bit[`VMM_RAL_DATA_WIDTH-1:0] value,
                          input  vmm_ral::path_e              path = vmm_ral::DEFAULT,
                          input  string                       domain = "",
                          input  int                          data_id = -1,
                          input  int                          scenario_id = -1,
                          input  int                          stream_id = -1);
   bit [`VMM_RAL_DATA_WIDTH-1:0] tmp;
   bit [`VMM_RAL_DATA_WIDTH-1:0] segval;
   bit [`VMM_RAL_ADDR_WIDTH-1:0] segoff;
   vmm_rw::status_e st;

   int flsb, lsb;
   int segsiz, segn;
   vmm_ral_mem    mem;

   mem = this.parent.get_memory();
   if (mem == null) begin
      `vmm_error(this.log, $psprintf("Cannot call vmm_ral_vfield::read() on unimplemented virtual register \"%s\"",
                                     this.get_fullname()));
      status = vmm_rw::ERROR;
      return;
   end

   if (path == vmm_ral::DEFAULT) begin
      vmm_ral_block blk = this.parent.get_block();
      path = blk.get_default_access();
   end

   status = vmm_rw::IS_OK;

   this.parent.XatomicX(1);

   value = 0;

   `foreach (this.XcbsX,j) begin
      vmm_ral_vfield_callbacks cb;
      if (!$cast(cb, this.XcbsX[j])) continue;
      cb.pre_read(this, idx, path, domain);
   end

   segsiz = mem.get_n_bytes() * 8;
   flsb    = this.get_lsb_pos_in_register();
   segoff  = this.parent.get_offset_in_memory(idx) + (flsb / segsiz);
   lsb = flsb % segsiz;

   // Total number of memory segment in this field
   segn = (lsb + this.get_n_bits() - 1) / segsiz + 1;

   // Read each of the segments, MSB first
   segoff += segn - 1;
   repeat (segn) begin
      value = value << segsiz;

      mem.read(st, segoff, tmp, path, domain,
               data_id, scenario_id, stream_id);
      if (st != vmm_rw::IS_OK) status = vmm_rw::ERROR;

      segoff--;
      value |= tmp;
   end

   // Any bits on the LSB side we need to get rid of?
   value = value >> lsb;

   // Any bits on the MSB side we need to get rid of?
   value &= (1<<this.get_n_bits()) - 1;

   `foreach (this.XcbsX,j) begin
      vmm_ral_vfield_callbacks cb;
      if (!$cast(cb, this.XcbsX[j])) continue;
      cb.post_read(this, idx, value, path, domain, status);
   end

   this.parent.XatomicX(0);

   `vmm_trace(this.log, $psprintf("Read virtual field \"%s\"[%0d] via %s: 'h%h",
                                  this.get_fullname(), idx,
                                  (path == vmm_ral::BFM) ? "frontdoor" : "backdoor",
                                  value));

endtask: read
               

task vmm_ral_vfield::poke(input  longint unsigned              idx,
                          output vmm_rw::status_e              status,
                          input  bit [`VMM_RAL_DATA_WIDTH-1:0] value,
                          input  int                           data_id = -1,
                          input  int                           scenario_id = -1,
                          input  int                           stream_id = -1);
   bit [`VMM_RAL_DATA_WIDTH-1:0] tmp;
   bit [`VMM_RAL_DATA_WIDTH-1:0] segval;
   bit [`VMM_RAL_ADDR_WIDTH-1:0] segoff;
   vmm_rw::status_e st;

   int flsb, fmsb, rmwbits;
   int segsiz, segn;
   vmm_ral_mem    mem;
   vmm_ral::path_e rm_path;

   mem = this.parent.get_memory();
   if (mem == null) begin
      `vmm_error(this.log, $psprintf("Cannot call vmm_ral_vfield::poke() on unimplemented virtual register \"%s\"",
                                     this.get_fullname()));
      status = vmm_rw::ERROR;
      return;
   end

   status = vmm_rw::IS_OK;

   this.parent.XatomicX(1);

   if (value >> this.size) begin
      `vmm_warning(log, $psprintf("Writing value 'h%h that is greater than field \"%s\" size (%0d bits)", value, this.get_fullname(), this.get_n_bits()));
      value &= value & ((1<<this.size)-1);
   end
   tmp = 0;

   segsiz = mem.get_n_bytes() * 8;
   flsb    = this.get_lsb_pos_in_register();
   segoff  = this.parent.get_offset_in_memory(idx) + (flsb / segsiz);

   // Any bits on the LSB side we need to RMW?
   rmwbits = flsb % segsiz;

   // Total number of memory segment in this field
   segn = (rmwbits + this.get_n_bits() - 1) / segsiz + 1;

   if (rmwbits > 0) begin
      bit [`VMM_RAL_ADDR_WIDTH-1:0] segn;

      mem.peek(st, segoff, tmp,
               data_id, scenario_id, stream_id);
      if (st != vmm_rw::IS_OK) begin
         `vmm_error(this.log,
                    $psprintf("Unable to read LSB bits in %s[%0d] to for RMW cycle on virtual field %s.",
                              mem.get_fullname(), segoff, this.get_fullname()));
         status = vmm_rw::ERROR;
         this.parent.XatomicX(0);
         return;
      end

      value = (value << rmwbits) | (tmp & ((1<<rmwbits)-1));
   end

   // Any bits on the MSB side we need to RMW?
   fmsb = rmwbits + this.get_n_bits() - 1;
   rmwbits = (fmsb+1) % segsiz;
   if (rmwbits > 0) begin
      if (segn > 0) begin
         mem.peek(st, segoff + segn - 1, tmp,
                  data_id, scenario_id, stream_id);
         if (st != vmm_rw::IS_OK) begin
            `vmm_error(this.log,
                       $psprintf("Unable to read MSB bits in %s[%0d] to for RMW cycle on virtual field %s.",
                                 mem.get_fullname(), segoff+segn-1,
                                 this.get_fullname()));
            status = vmm_rw::ERROR;
            this.parent.XatomicX(0);
            return;
         end
      end
      value |= (tmp & ~((1<<rmwbits)-1)) << ((segn-1)*segsiz);
   end

   // Now write each of the segments
   tmp = value;
   repeat (segn) begin
      mem.poke(st, segoff, tmp,
               data_id, scenario_id, stream_id);
      if (st != vmm_rw::IS_OK) status = vmm_rw::ERROR;

      segoff++;
      tmp = tmp >> segsiz;
   end

   this.parent.XatomicX(0);

   `vmm_trace(this.log, $psprintf("Wrote virtual field \"%s\"[%0d] with: 'h%h",
                                  this.get_fullname(), idx, value));

endtask: poke


task vmm_ral_vfield::peek(input  longint unsigned             idx,
                          output vmm_rw::status_e             status,
                          output bit[`VMM_RAL_DATA_WIDTH-1:0] value,
                          input  int                          data_id = -1,
                          input  int                          scenario_id = -1,
                          input  int                          stream_id = -1);
   bit [`VMM_RAL_DATA_WIDTH-1:0] tmp;
   bit [`VMM_RAL_DATA_WIDTH-1:0] segval;
   bit [`VMM_RAL_ADDR_WIDTH-1:0] segoff;
   vmm_rw::status_e st;

   int flsb, lsb;
   int segsiz, segn;
   vmm_ral_mem    mem;

   mem = this.parent.get_memory();
   if (mem == null) begin
      `vmm_error(this.log, $psprintf("Cannot call vmm_ral_vfield::peek() on unimplemented virtual register \"%s\"",
                                     this.get_fullname()));
      status = vmm_rw::ERROR;
      return;
   end

   status = vmm_rw::IS_OK;

   this.parent.XatomicX(1);

   value = 0;

   segsiz = mem.get_n_bytes() * 8;
   flsb    = this.get_lsb_pos_in_register();
   segoff  = this.parent.get_offset_in_memory(idx) + (flsb / segsiz);
   lsb = flsb % segsiz;

   // Total number of memory segment in this field
   segn = (lsb + this.get_n_bits() - 1) / segsiz + 1;

   // Read each of the segments, MSB first
   segoff += segn - 1;
   repeat (segn) begin
      value = value << segsiz;

      mem.peek(st, segoff, tmp,
               data_id, scenario_id, stream_id);
      if (st != vmm_rw::IS_OK) status = vmm_rw::ERROR;

      segoff--;
      value |= tmp;
   end

   // Any bits on the LSB side we need to get rid of?
   value = value >> lsb;

   // Any bits on the MSB side we need to get rid of?
   value &= (1<<this.get_n_bits()) - 1;

   this.parent.XatomicX(0);

   `vmm_trace(this.log, $psprintf("Peeked virtual field \"%s\"[%0d]: 'h%h",
                                  this.get_fullname(), idx, value));

endtask: peek
               

function void vmm_ral_vfield::prepend_callback(vmm_ral_vfield_callbacks cb);
   `foreach (this.XcbsX,i) begin
      if (this.XcbsX[i] == cb) begin
         `vmm_warning(this.log, $psprintf("Callback has already been registered with field \"%s\"", this.get_fullname()));
         return;
      end
   end
   
   // Prepend new callback
   this.XcbsX.push_front(cb);
endfunction: prepend_callback


function void vmm_ral_vfield::append_callback(vmm_ral_vfield_callbacks cb);
   `foreach (this.XcbsX,i) begin
      if (this.XcbsX[i] == cb) begin
         `vmm_warning(this.log, $psprintf("Callback has already been registered with field \"%s\"", this.get_fullname()));
         return;
      end
   end
   
   // Append new callback
   this.XcbsX.push_back(cb);
endfunction: append_callback


function void vmm_ral_vfield::unregister_callback(vmm_ral_vfield_callbacks cb);
   `foreach (this.XcbsX,i) begin
      if (this.XcbsX[i] == cb) begin
         int j = i;
         // Unregister it
         this.XcbsX.delete(j);
         return;
      end
   end

   `vmm_warning(this.log, $psprintf("Callback was not registered with field \"%s\"", this.get_fullname()));
endfunction: unregister_callback
