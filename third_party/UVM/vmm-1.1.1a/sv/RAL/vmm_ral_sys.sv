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


class vmm_ral_sys_domain;
   vmm_ral_block blocks[$];
   string        blk_domains[$];
   vmm_ral_sys   subsys[$];
   string        sys_domains[$];
endclass


class vmm_ral_sys extends vmm_ral_block_or_sys;
   local vmm_ral_sys_domain domains[];

   extern function new(
                       vmm_ral_sys                   parent = null,
                       string                        name,
                       string                        typename,
                       int unsigned                  n_bytes,
                       vmm_ral::endianness_e         endian,
                       bit [`VMM_RAL_ADDR_WIDTH-1:0] base_addr = 0,
                       string                        domain    = "",
                       int                           cover_on  = vmm_ral::NO_COVERAGE,
                       int                           has_cover  = vmm_ral::NO_COVERAGE);

   /*local*/ extern virtual function void Xlock_modelX();
   /*local*/ extern virtual function void add_domain(int unsigned          n_bytes,
                                                     vmm_ral::endianness_e endian,
                                                     string                domain);
   /*local*/ extern function void register_block(vmm_ral_block                 block,
                                                 string                        domain = "",
                                                 string                        in_domain = "",
                                                 bit [`VMM_RAL_ADDR_WIDTH-1:0] base_addr);
   /*local*/ extern function void register_subsys(vmm_ral_sys                  subsys,
                                                  string                       domain = "",
                                                  string                       in_domain = "",
                                                  bit [`VMM_RAL_ADDR_WIDTH-1:0]base_addr);
   /*local*/ extern virtual function void Xregister_ral_accessX(vmm_ral_access access);

   extern virtual function string psdisplay(string prefix = "",
                                            string domain = "");

   extern virtual function void get_fields(ref vmm_ral_field fields[],
                                           input string      domain = ""); 
   extern virtual function void get_virtual_fields(ref vmm_ral_vfield fields[],
                                                   input string      domain = ""); 
   extern virtual function vmm_ral_field get_field_by_name(string name);
   extern virtual function vmm_ral_vfield get_virtual_field_by_name(string name);

   extern virtual function void get_registers(ref vmm_ral_reg regs[],
                                              input string    domain = "");
   extern virtual function void get_virtual_registers(ref vmm_ral_vreg vregs[],
                                                      input string    domain = "");
   extern virtual function vmm_ral_reg get_reg_by_name(string name);
   extern virtual function vmm_ral_vreg get_vreg_by_name(string name);

   extern local   function vmm_ral_reg Xget_reg_by_offsetX(bit [`VMM_RAL_ADDR_WIDTH-1:0] offset,
                                                           string                        domain = "");

   extern virtual function vmm_ral_reg get_reg_by_offset(bit [`VMM_RAL_ADDR_WIDTH-1:0] offset,
                                                         string                        domain = "");
   extern virtual function vmm_ral_vreg get_vreg_by_offset(bit [`VMM_RAL_ADDR_WIDTH-1:0] offset,
                                                           string                        domain = "");

   extern virtual function void get_memories(ref vmm_ral_mem mems[],
                                             input string    domain = "");
   extern virtual function vmm_ral_mem get_mem_by_name(string name);
   extern virtual function vmm_ral_mem get_mem_by_offset(bit [`VMM_RAL_ADDR_WIDTH-1:0] offset,
                                                         string                        domain = "");

   extern virtual function void get_blocks(ref vmm_ral_block blocks[],
                                           ref string        domains[],
                                           input string      domain = "");
   extern virtual function void get_all_blocks(ref vmm_ral_block blocks[],
                                               ref string        domains[],
                                               input string      domain = "");
   extern virtual function vmm_ral_block get_block_by_name(string name);  
   extern virtual function vmm_ral_block get_block_by_offset(bit [`VMM_RAL_ADDR_WIDTH-1:0] offset,
                                                             string                        domain = ""); 

   extern virtual function void get_subsys(ref vmm_ral_sys subsys[],
                                           ref string      domains[],
                                           input string    domain = ""); 
   extern virtual function void get_all_subsys(ref vmm_ral_sys subsys[],
                                               ref string      domains[],
                                               input string    domain = ""); 
   extern virtual function vmm_ral_sys get_subsys_by_name(string name);  
   extern virtual function vmm_ral_sys get_subsys_by_offset(bit [`VMM_RAL_ADDR_WIDTH-1:0] offset,
                                                            string                        domain = ""); 
     
   extern virtual function void ral_power_down(bit retain = 0);
   extern virtual function void ral_power_up(string power_domains = "");

   extern function int set_cover(int is_on);

   extern virtual function void reset(string           domain = "",
                                      vmm_ral::reset_e kind   = vmm_ral::HARD); 
   extern virtual function bit needs_update();

   extern virtual task update(output vmm_rw::status_e status,
                              input  vmm_ral::path_e  path = vmm_ral::DEFAULT);
   extern virtual task mirror(output vmm_rw::status_e status,
                              input  vmm_ral::check_e check = vmm_ral::	QUIET,
                              input  vmm_ral::path_e  path  = vmm_ral::DEFAULT);
   
   extern virtual task readmemh(string filename);
   extern virtual task writememh(string filename);

   extern function int unsigned get_sys_ID();

   extern virtual function int unsigned get_block_or_sys_size(string domain = "");

   extern virtual function bit set_offset(bit [`VMM_RAL_ADDR_WIDTH-1:0] offset,
                                          string domain = "");


   extern virtual function bit Xcheck_child_overlapX(int unsigned my_offset,
                                                     int unsigned my_size,
                                                     string domain = "",
                                                     vmm_ral_block blk,
                                                     vmm_ral_sys sys);



endclass: vmm_ral_sys


function vmm_ral_sys::new(vmm_ral_sys                   parent = null,
                          string                        name,
                          string                        typename,
                          int unsigned                  n_bytes,
                          vmm_ral::endianness_e         endian,
                          bit [`VMM_RAL_ADDR_WIDTH-1:0] base_addr = 0,
                          string                        domain = "",
                          int                           cover_on = vmm_ral::NO_COVERAGE,
                          int                           has_cover = vmm_ral::NO_COVERAGE);
   super.new(parent, "RAL System", name, typename,
             n_bytes, endian, base_addr, domain,
             cover_on, has_cover);

   this.domains = new [1];
   this.domains[0] = new;
endfunction: new


function void vmm_ral_sys::Xlock_modelX();
   if (this.Xis_lockedX()) return;

   super.Xlock_modelX();
   `foreach (this.domains,i) begin
      `foreach (this.domains[i].blocks,j) begin
         this.domains[i].blocks[j].Xlock_modelX();
      end
      `foreach (this.domains[i].subsys,j) begin
         this.domains[i].subsys[j].Xlock_modelX();
      end
   end
endfunction: Xlock_modelX


function void vmm_ral_sys::add_domain(int unsigned          n_bytes,
                                      vmm_ral::endianness_e endian,
                                      string                domain);
   int n;

   super.add_domain(n_bytes, endian, domain);

   n = this.domains.size();
   this.domains    = new [n+1] (this.domains);
   this.domains[n] = new;
endfunction: add_domain


function void vmm_ral_sys::register_block(vmm_ral_block                 block,
                                          string                        domain = "",
                                          string                        in_domain = "",
                                          bit [`VMM_RAL_ADDR_WIDTH-1:0] base_addr);
   string doms[];
   vmm_ral_sys_domain dom;

   if (this.Xis_lockedX()) begin
      `vmm_error(this.log, "Cannot add block to locked system model");
      return;
   end

   block.get_domains(doms);
   foreach (doms[i]) begin
      if (doms[i] == domain) begin
         int j = this.get_domain_index(in_domain);
         if (j < 0) return;

         dom = this.domains[j];
         dom.blocks.push_back(block);
         dom.blk_domains.push_back(domain);

         begin
            int k;
            j = this.get_n_bytes(in_domain);
            k = block.get_n_bytes(domain);
            if (k > j) begin
               `vmm_warning(this.log, $psprintf("%0d-byte block %s.%s instantiated in %0d-byte system %s.%s",
                                                k, block.get_name(), domain,
                                                j, this.get_name(), in_domain));
            end
         end

         block.map_domain(domain, in_domain, base_addr);

         return;
      end
   end

   `vmm_error(this.log, $psprintf("Domain \"%s\" not found in block \"%s\".",
                                  domain, block.get_name()));
endfunction: register_block



function void vmm_ral_sys::register_subsys(vmm_ral_sys                   subsys,
                                           string                        domain = "",
                                           string                        in_domain = "",
                                           bit [`VMM_RAL_ADDR_WIDTH-1:0] base_addr);
   string doms[];
   vmm_ral_sys_domain dom;
   int i;

   if (this.Xis_lockedX()) begin
      `vmm_error(this.log, "Cannot add subsystem to locked system model");
      return;
   end

   subsys.get_domains(doms);
   foreach (doms[i]) begin
      if (doms[i] == domain) begin
         int j = this.get_domain_index(in_domain);
         if (j < 0) return;

         dom = this.domains[j];
         dom.subsys.push_back(subsys);
         dom.sys_domains.push_back(domain);

         begin
            int k;
            j = this.get_n_bytes(in_domain);
            k = subsys.get_n_bytes(domain);
            if (k > j) begin
               `vmm_warning(this.log, $psprintf("%0d-byte system %s.%s instantiated in %0d-byte system %s.%s",
                                                k, subsys.get_name(), domain,
                                                j, this.get_name(), in_domain));
            end
         end

         subsys.map_domain(domain, in_domain, base_addr);

         return;
      end
   end

   `vmm_error(this.log, $psprintf("Domain \"%s\" not found in system \"%s\".",
                                  domain, subsys.get_fullname()));
endfunction: register_subsys


function void vmm_ral_sys::Xregister_ral_accessX(vmm_ral_access access);
   // There can only be one RAL Access on a RAL model
   if (this.ral_access != null && this.ral_access != access) begin
      `vmm_fatal(this.log, $psprintf("System %s is already used by another RAL access instance", this.get_fullname()));
   end
   this.ral_access = access;

   // Register all sub-elements
   begin
      vmm_ral_sys sys[];
      vmm_ral_block blks[];
      string domains[];

      this.get_subsys(sys, domains);
      foreach (sys[i]) begin
         sys[i].Xregister_ral_accessX(access);
      end

      this.get_blocks(blks, domains);
      foreach (blks[i]) begin
         blks[i].Xregister_ral_accessX(access);
      end
   end
endfunction: Xregister_ral_accessX


function string vmm_ral_sys::psdisplay(string prefix = "",
                                       string domain = "");
   string image;
   string domains[];
   string blk_domains[];
   vmm_ral_sys sys[];
   vmm_ral_block blks[];
   bit         single_domain;
   vmm_ral::endianness_e endian;

   single_domain = 1;
   if (domain == "") begin
      this.get_domains(domains);
      if (domains.size() > 1) single_domain = 0;
   end

   if (single_domain) begin
      $sformat(image, "%sSystem %s", prefix, this.get_fullname());
      if (domain != "") $sformat(image, "%s.%s", image, domain);
      endian = this.get_endian(domain);
      $sformat(image, "%s -- %0d bytes (%s)", image,
               this.get_n_bytes(domain), endian.name());

      this.get_blocks(blks, blk_domains, domain);
      foreach (blks[i]) begin
         string img;
         img = blks[i].psdisplay({prefix, "   "}, blk_domains[i]);
         image = {image, "\n", img};
      end

      this.get_subsys(sys, blk_domains, domain);
      foreach (sys[i]) begin
         string img;
         img = sys[i].psdisplay({prefix, "   "}, blk_domains[i]);
         image = {image, "\n", img};
      end
   end
   else begin
      $sformat(image, "%sSystem %s", prefix, this.get_fullname());
      foreach (domains[i]) begin
         string img;
         endian = this.get_endian(domains[i]);
         $sformat(img, "%s   Domain \"%s\" -- %0d bytes (%s)",
                  prefix, domains[i],
                  this.get_n_bytes(domains[i]), endian.name());
         image = {image, "\n", img};

         this.get_blocks(blks, blk_domains, domains[i]);
         foreach (blks[j]) begin
            img = blks[j].psdisplay({prefix, "      "},
                                    blk_domains[j]);
            image = {image, "\n", img};
         end

         this.get_subsys(sys, blk_domains, domains[i]);
         foreach (sys[j]) begin
            img = sys[j].psdisplay({prefix, "      "},
                                   blk_domains[j]);
            image = {image, "\n", img};
         end
      end
   end
   return image;
endfunction: psdisplay


function void vmm_ral_sys::get_fields(ref vmm_ral_field fields[],
                                      input string      domain = "");
   int n;
   vmm_ral_block b[];
   string        d[];
   vmm_ral_field f[];

   this.get_all_blocks(b, d, domain);
   fields = new [0];
   foreach (b[i]) begin
      b[i].get_fields(f, d[i]);
      n = fields.size();
      fields = new [n + f.size()] (fields);

      foreach (f[j]) begin
         fields[n++] = f[j];
      end
   end
endfunction: get_fields

function void vmm_ral_sys::get_virtual_fields(ref vmm_ral_vfield fields[],
                                              input string      domain = "");
   int n;
   vmm_ral_block b[];
   string        d[];
   vmm_ral_vfield f[];

   this.get_all_blocks(b, d, domain);
   fields = new [0];
   foreach (b[i]) begin
      b[i].get_virtual_fields(f, d[i]);
      n = fields.size();
      fields = new [n + f.size()] (fields);

      foreach (f[j]) begin
         fields[n++] = f[j];
      end
   end
endfunction: get_virtual_fields

function vmm_ral_field vmm_ral_sys::get_field_by_name(string name);
   // Search the registers to find the first field of the specified name
   vmm_ral_reg r[];

   this.get_registers(r);
   foreach (r[i]) begin
      vmm_ral_field fields[];
      r[i].get_fields(fields);
      foreach (fields[j]) begin
         if (fields[j].get_name() == name) begin
            return fields[j];
         end
      end
   end
   `vmm_warning(this.log, $psprintf("Unable to locate field \"%s\" in system \"%s\".",
                                    name, this.get_fullname()));
   get_field_by_name = null;
endfunction: get_field_by_name

function vmm_ral_vfield vmm_ral_sys::get_virtual_field_by_name(string name);
   // Search the registers to find the first field of the specified name
   vmm_ral_vreg r[];

   this.get_virtual_registers(r);
   foreach (r[i]) begin
      vmm_ral_vfield fields[];
      r[i].get_fields(fields);
      foreach (fields[j]) begin
         if (fields[j].get_name() == name) begin
            return fields[j];
         end
      end
   end
   `vmm_warning(this.log, $psprintf("Unable to locate virtual field \"%s\" in system \"%s\".",
                                    name, this.get_fullname()));
   get_virtual_field_by_name = null;
endfunction: get_virtual_field_by_name

function void vmm_ral_sys::get_registers(ref vmm_ral_reg regs[],
                                         input string    domain = "");
   vmm_ral_block blks[];
   string        d[];
   
   regs = new [0];

   this.get_all_blocks(blks, d, domain);
   foreach (blks[i]) begin
      int n = regs.size();
      vmm_ral_reg rg[];
      
      blks[i].get_registers(rg, d[i]);
      regs = new [n + rg.size()] (regs);

      foreach (rg[j]) begin
         regs[n+j] = rg[j];
      end
   end
endfunction: get_registers

function void vmm_ral_sys::get_virtual_registers(ref vmm_ral_vreg vregs[],
                                                 input string    domain = "");
   vmm_ral_block blks[];
   string        d[];
   
   vregs = new [0];

   this.get_all_blocks(blks, d, domain);
   foreach (blks[i]) begin
      int n = vregs.size();
      vmm_ral_vreg rg[];
      
      blks[i].get_virtual_registers(rg, d[i]);
      vregs = new [n + rg.size()] (vregs);

      foreach (rg[j]) begin
         vregs[n+j] = rg[j];
      end
   end
endfunction: get_virtual_registers

function vmm_ral_reg vmm_ral_sys::get_reg_by_name(string name);
   // Search the registers to find the first of the specified name
   vmm_ral_reg r[];

   this.get_registers(r);
   foreach (r[i]) begin
      if (r[i].get_name() == name) begin
         return r[i];
      end
   end
   `vmm_warning(this.log, $psprintf("Unable to locate register \"%s\" in system \"%s\".",
                                    name, this.get_fullname()));
   get_reg_by_name = null;
endfunction: get_reg_by_name

function vmm_ral_vreg vmm_ral_sys::get_vreg_by_name(string name);
   // Search the registers to find the first of the specified name
   vmm_ral_vreg r[];

   this.get_virtual_registers(r);
   foreach (r[i]) begin
      if (r[i].get_name() == name) begin
         return r[i];
      end
   end
   `vmm_warning(this.log, $psprintf("Unable to locate virtual register \"%s\" in system \"%s\".",
                                    name, this.get_fullname()));
   get_vreg_by_name = null;
endfunction: get_vreg_by_name


function vmm_ral_reg vmm_ral_sys::Xget_reg_by_offsetX(bit [`VMM_RAL_ADDR_WIDTH-1:0] offset,
                                                    string                        domain = "");
   vmm_ral_sys_domain dom; int unsigned my_n_bytes;
   int j = this.get_domain_index(domain);
   if (j < 0) begin
      `vmm_warning(this.log, $psprintf("Unable to locate domain \"%s\" in System \"%s\".",
                                       domain, this.get_fullname()));
      return null;
   end
   my_n_bytes = this.get_n_bytes(domain); 
   dom = this.domains[j];

   // Look inside all blocks... 
   `foreach (dom.blocks,i) begin
      bit [`VMM_RAL_ADDR_WIDTH-1:0] tmp_offset = dom.blocks[i].get_base_addr(dom.blk_domains[i]); 
      if (tmp_offset <= offset) begin
`ifdef VMM_RAL_FAST_SRCH
         int unsigned blk_n_bytes = dom.blocks[i].get_n_bytes(dom.blk_domains[i]);
         bit [`VMM_RAL_ADDR_WIDTH-1:0] reg_offset = offset - tmp_offset;
         int unsigned multiplier = (((blk_n_bytes-1)/my_n_bytes)+1);

         if ((reg_offset % multiplier) == 0) begin
            vmm_ral_reg_by_offset_map reg_map = dom.blocks[i].Xget_reg_by_offset_mapX(dom.blk_domains[i]);
            bit [`VMM_RAL_ADDR_WIDTH-1:0] reg_offset_in_blk = reg_offset / multiplier;
            if (reg_map.reg_by_offset.exists(reg_offset_in_blk))
               return reg_map.reg_by_offset[reg_offset_in_blk];
         end
`else
         vmm_ral_reg regs[];
         int unsigned blk_n_bytes = dom.blocks[i].get_n_bytes(dom.blk_domains[i]);
         bit [`VMM_RAL_ADDR_WIDTH-1:0] reg_offset = offset - tmp_offset;
         dom.blocks[i].get_registers(regs, dom.blk_domains[i]);
         foreach (regs[k]) begin
            if ((regs[k].get_offset_in_block(dom.blk_domains[i]) * 
               (((blk_n_bytes-1)/my_n_bytes)+1)) == reg_offset)
                  return regs[k];
         end
`endif
      end
   end

   // Look inside all sub-systems...
   `foreach (dom.subsys,i) begin
      bit [`VMM_RAL_ADDR_WIDTH-1:0] tmp_offset = dom.subsys[i].get_base_addr(dom.sys_domains[i]); 
      if (tmp_offset <= offset) begin
         vmm_ral_reg rg;
         bit [`VMM_RAL_ADDR_WIDTH-1:0] reg_offset = offset - tmp_offset;
         int unsigned sys_n_bytes = dom.subsys[i].get_n_bytes(dom.sys_domains[i]);
         if (sys_n_bytes > my_n_bytes) begin
            reg_offset = reg_offset / (((sys_n_bytes-1)/my_n_bytes)+1);
         end
         rg = dom.subsys[i].Xget_reg_by_offsetX(reg_offset, dom.sys_domains[i]);
         if (rg) return rg;
      end
   end

   Xget_reg_by_offsetX = null;
endfunction: Xget_reg_by_offsetX


function vmm_ral_reg vmm_ral_sys::get_reg_by_offset(bit [`VMM_RAL_ADDR_WIDTH-1:0] offset,
                                                    string                        domain = "");
   vmm_ral_reg rg = this.Xget_reg_by_offsetX(offset, domain);

   if (rg) return rg;

   `vmm_warning(this.log, $psprintf("Unable to locate register at offset 0x%h %0sin system \"%s\".",
                                    offset, ((domain == "") ? "" : $psprintf("in domain \"%s\" ",
                                    domain)), this.get_fullname()));
   get_reg_by_offset = null;
endfunction: get_reg_by_offset


function vmm_ral_vreg vmm_ral_sys::get_vreg_by_offset(bit [`VMM_RAL_ADDR_WIDTH-1:0] offset,
                                                      string                        domain = "");
   return null;
endfunction: get_vreg_by_offset
                                                    
function void vmm_ral_sys::get_memories(ref vmm_ral_mem mems[],
                                        input string    domain = "");
   vmm_ral_block blks[];
   string        d[];
   
   mems = new [0];

   this.get_all_blocks(blks, d, domain);
   foreach (blks[i]) begin
      integer n = mems.size();
      vmm_ral_mem mm[];
      
      blks[i].get_memories(mm, domain);
      mems = new [n + mm.size()] (mems);

      foreach (mm[j]) begin
         mems[n+j] = mm[j];
      end
   end
endfunction: get_memories


function vmm_ral_mem vmm_ral_sys::get_mem_by_name(string name);
   // Search the memories to find the first of the specified name
   vmm_ral_mem m[];

   this.get_memories(m);
   foreach (m[i]) begin
      if (m[i].get_name() == name) begin
         return m[i];
      end
   end
   `vmm_warning(this.log, $psprintf("Unable to locate memory \"%s\" in system \"%s\".",
                                    name, this.get_fullname()));
   get_mem_by_name = null;
endfunction: get_mem_by_name


function vmm_ral_mem vmm_ral_sys::get_mem_by_offset(bit [`VMM_RAL_ADDR_WIDTH-1:0] offset,
                                                    string                        domain = "");
   return null;
endfunction: get_mem_by_offset

                                                    
function void vmm_ral_sys::get_blocks(ref vmm_ral_block blocks[],
                                      ref string        domains[],
                                      input string      domain = "");
   if (domain == "" && this.domains.size() > 1) begin
      blocks = new [0];
      domains = new [0];

      `foreach (this.domains,i) begin
         int n = blocks.size();
      
         blocks  = new [n + this.domains[i].blocks.size()] (blocks);
         domains = new [n + this.domains[i].blocks.size()] (domains);
      
         `foreach (this.domains[i].blocks,j) begin
            blocks[n+j]  = this.domains[i].blocks[j];
            domains[n+j] = this.domains[i].blk_domains[j];
         end
      end
   end
   else begin
      vmm_ral_sys_domain dom;
      int i;

      i = this.get_domain_index(domain);
      if (i < 0) return;

      dom = this.domains[i];
      blocks = new [dom.blocks.size()];
      domains = new [dom.blocks.size()];
      
      `foreach (dom.blocks,j) begin
         blocks[j]  = dom.blocks[j];
         domains[j] = dom.blk_domains[j];
      end
   end
endfunction: get_blocks

                             
function void vmm_ral_sys::get_all_blocks(ref vmm_ral_block blocks[],
                                          ref string        domains[],
                                          input string      domain = "");
   vmm_ral_block blks[];
   vmm_ral_sys   sys[];
   string        doms[];
   string        subdoms[];
   
   this.get_blocks(blocks, domains, domain);

   this.get_all_subsys(sys, subdoms, domain);
   foreach (sys[i]) begin
      int n = blocks.size();
      
      sys[i].get_blocks(blks, doms, subdoms[i]);
      blocks  = new [n + blks.size()] (blocks);
      domains = new [n + blks.size()] (domains);
      
      foreach (blks[j]) begin
         blocks[n+j] = blks[j];
         domains[n+j] = doms[j];
      end
   end
endfunction: get_all_blocks

                             
function vmm_ral_block vmm_ral_sys::get_block_by_name(string name);
   vmm_ral_block blks[];
   string        d[];

   this.get_all_blocks(blks, d);
   foreach (blks[i]) begin
      if (blks[i].get_name() == name) begin
         return blks[i];
      end
   end
   `vmm_warning(this.log, $psprintf("Unable to locate block \"%s\" in system \"%s\".",
                                    name, this.get_fullname()));
   get_block_by_name = null;
endfunction: get_block_by_name


function vmm_ral_block vmm_ral_sys::get_block_by_offset(bit [`VMM_RAL_ADDR_WIDTH-1:0] offset,
                                                        string                        domain = "");
   return null;
endfunction: get_block_by_offset

                                                        
function void vmm_ral_sys::get_subsys(ref vmm_ral_sys subsys[],
                                      ref string      domains[],
                                      input string    domain = "");
   if (domain == "" && this.domains.size() > 1) begin
      subsys  = new [0];
      domains = new [0];

      `foreach (this.domains,i) begin
         int n = subsys.size();
      
         subsys  = new [n + this.domains[i].subsys.size()] (subsys);
         domains = new [n + this.domains[i].subsys.size()] (domains);
      
         `foreach (this.domains[i].subsys,j) begin
            subsys[n+j]  = this.domains[i].subsys[j];
            domains[n+j] = this.domains[i].sys_domains[j];
         end
      end
   end
   else begin
      vmm_ral_sys_domain dom;
      int i;

      i = this.get_domain_index(domain);
      if (i < 0) return;

      dom = this.domains[i];
      subsys = new [dom.subsys.size()];
      domains = new [dom.subsys.size()];

      `foreach (dom.subsys,j) begin
         subsys[j]  = dom.subsys[j];
         domains[j] = dom.sys_domains[j];
      end
   end
endfunction: get_subsys


function void vmm_ral_sys::get_all_subsys(ref vmm_ral_sys subsys[],
                                          ref string      domains[],
                                          input string    domain = "");
   vmm_ral_sys   sys[];
   string        subdoms[];
   vmm_ral_sys   ss[];
   string        doms[];

   subsys  = new [0];
   domains = new[0];

   this.get_subsys(sys, subdoms, domain);

   foreach (sys[i]) begin
      int n = subsys.size() + 1;
      
      sys[i].get_all_subsys(ss, doms, subdoms[i]);
      subsys  = new [n + ss.size()] (subsys);
      domains = new [n + ss.size()] (domains);

      subsys[n-1]  = sys[i];
      domains[n-1] = subdoms[i];

      foreach (ss[j]) begin
         subsys[n+j]  = ss[j];
         domains[n+j] = doms[j];
      end
   end
endfunction: get_all_subsys


function vmm_ral_sys vmm_ral_sys::get_subsys_by_name(string name);
   vmm_ral_sys subsys[];
   string      d[];

   this.get_all_subsys(subsys, d);
   foreach (subsys[i]) begin
      if (subsys[i].get_name() == name) begin
         return subsys[i];
      end
   end
   `vmm_warning(this.log, $psprintf("Unable to locate subsystem \"%s\" in system \"%s\".",
                                    name, this.get_fullname()));
   get_subsys_by_name = null;
endfunction: get_subsys_by_name


function vmm_ral_sys vmm_ral_sys::get_subsys_by_offset(bit [`VMM_RAL_ADDR_WIDTH-1:0] offset,
                                                       string                        domain = "");
   return null;
endfunction: get_subsys_by_offset

                                                       
function void vmm_ral_sys::ral_power_down(bit retain = 0);
   vmm_ral_block blks[];
   string        domains[];

   // Power down all blocks
   this.get_blocks(blks, domains);
   foreach (blks[i]) begin
      blks[i].ral_power_down(retain);
   end
endfunction: ral_power_down


function void vmm_ral_sys::ral_power_up(string power_domains = "");
   vmm_ral_block blks[];
   string        domains[];
   string        pwr_domain;

   if (power_domains != "") begin
      pwr_domain = this.get_attribute("POWER_DOMAIN");
      if (!`vmm_str_match(pwr_domain, power_domains)) return;
   end

   // Power up blocks in the specified power domains
   this.get_blocks(blks, domains);
   foreach (blks[i]) begin
      if (power_domains != "") begin
         pwr_domain = blks[i].get_attribute("POWER_DOMAIN");
         if (!`vmm_str_match(pwr_domain, power_domains)) continue;
      end
      blks[i].ral_power_up(power_domains);
   end
endfunction: ral_power_up


function int vmm_ral_sys::set_cover(int is_on);
   int can_cvr;

   set_cover = super.set_cover(is_on);
   can_cvr = is_on & set_cover; 
   if (can_cvr == 0) return set_cover;

   `foreach (this.domains,i) begin
      `foreach (this.domains[i].blocks,j) begin
         void'(this.domains[i].blocks[j].set_cover(can_cvr));
      end
      `foreach (this.domains[i].subsys,j) begin
         void'(this.domains[i].subsys[j].set_cover(can_cvr));
      end
   end
endfunction: set_cover


function void vmm_ral_sys::reset(string           domain = "",
                                 vmm_ral::reset_e kind = vmm_ral::HARD);
   if (domain == "" && this.domains.size() > 1) begin
      `foreach (this.domains,i) begin
         `foreach (this.domains[i].blocks,j) begin
            this.domains[i].blocks[j].reset(this.domains[i].blk_domains[j],
                                            kind);
         end
         `foreach (this.domains[i].subsys,j) begin
            this.domains[i].subsys[j].reset(this.domains[i].sys_domains[j],
                                            kind);
         end
      end
   end
   else begin
      int i;

      i = this.get_domain_index(domain);
      if (i < 0) return;

      `foreach (this.domains[i].blocks,j) begin
         this.domains[i].blocks[j].reset(this.domains[i].blk_domains[j],
                                         kind);
      end
      `foreach (this.domains[i].subsys,j) begin
         this.domains[i].subsys[j].reset(this.domains[i].sys_domains[j],
                                         kind);
      end
   end
endfunction: reset


function bit vmm_ral_sys::needs_update();
   needs_update = 0;
   `foreach (this.domains,i) begin
      `foreach (this.domains[i].blocks,j) begin
         if (this.domains[i].blocks[j].needs_update()) begin
            return 1;
         end
      end
      `foreach (this.domains[i].subsys,j) begin
         if (this.domains[i].subsys[j].needs_update()) begin
            return 1;
         end
      end
   end
   return 0;
endfunction: needs_update


task vmm_ral_sys::update(output vmm_rw::status_e status,
                         input  vmm_ral::path_e  path = vmm_ral::DEFAULT);
   status = vmm_rw::IS_OK;
   `foreach (this.domains,i) begin
      `foreach (this.domains[i].blocks,j) begin
         this.domains[i].blocks[j].update(status, path);
         if (status != vmm_rw::IS_OK) return;
      end
      `foreach (this.domains[i].subsys,j) begin
         this.domains[i].subsys[j].update(status, path);
         if (status != vmm_rw::IS_OK) return;
      end
   end
endtask: update


task vmm_ral_sys::mirror(output vmm_rw::status_e status,
                         input  vmm_ral::check_e check = vmm_ral::QUIET,
                         input  vmm_ral::path_e  path = vmm_ral::DEFAULT);
   status = vmm_rw::IS_OK;
   `foreach (this.domains,i) begin
      `foreach (this.domains[i].blocks,j) begin
         this.domains[i].blocks[j].mirror(status, check, path);
         if (status != vmm_rw::IS_OK) return;
      end
      `foreach (this.domains[i].subsys,j) begin
         this.domains[i].subsys[j].mirror(status, check, path);
         if (status != vmm_rw::IS_OK) return;
      end
   end
endtask: mirror


task vmm_ral_sys::readmemh(string filename);
endtask: readmemh


task vmm_ral_sys::writememh(string filename);
endtask: writememh


function int unsigned vmm_ral_sys::get_sys_ID();
   get_sys_ID =  this.get_block_or_sys_ID();
endfunction

function int unsigned vmm_ral_sys::get_block_or_sys_size(string domain = "");

  vmm_ral_sys subsys[];
  vmm_ral_block blks[];
  string dm[];
  int j;
  int unsigned max_addr = 0;
  int unsigned size     = 1;

  j = this.get_domain_index(domain);
  if (j < 0)
  begin
     `vmm_warning(this.log, $psprintf("Unable to locate domain \"%s\" in system \"%s\".",
                                      domain, this.get_fullname()));
     get_block_or_sys_size = 0;
     return 0;
  end

  j =0;
  this.get_subsys(subsys,dm,domain);
  foreach(subsys[j])
  begin
    int unsigned offset_sys;
    offset_sys = subsys[j].get_base_addr(dm[j]);
    if(offset_sys >= max_addr)
    begin
      max_addr = offset_sys + 
                 ((subsys[j].get_block_or_sys_size(dm[j]) * 
                  ((((subsys[j].get_n_bytes(dm[j]) - 1)/this.get_n_bytes(domain))+1)))
                 ) - 1;
    end
  end

  j =0;
  this.get_blocks(blks,dm,domain);
  foreach(blks[j])
  begin
    int unsigned offset_blk;
    offset_blk = blks[j].get_base_addr(dm[j]);
    if(offset_blk >= max_addr)
    begin
      max_addr = offset_blk +
                 ((blks[j].get_block_or_sys_size(dm[j]) * 
                  ((((blks[j].get_n_bytes(dm[j]) - 1)/this.get_n_bytes(domain))+1)))
                 ) - 1;
    end
  end

  get_block_or_sys_size = max_addr + 1;

endfunction:get_block_or_sys_size

function bit vmm_ral_sys::set_offset(bit [`VMM_RAL_ADDR_WIDTH-1:0] offset,
                                     string domain = "");

  int j;
  vmm_ral_sys parent_sys;
  string parent_domain;

  set_offset = 0;
  j = this.get_domain_index(domain);
  if (j < 0)
  begin
     `vmm_warning(this.log, $psprintf("Unable to locate domain \"%s\" in Block \"%s\".",
                                      domain, this.get_fullname()));
     return 0;
  end

  if(this.get_parent() != null)
  begin
    parent_sys = this.get_parent();
    parent_domain = this.get_parent_domain(domain);
    if(!parent_sys.Xcheck_child_overlapX(offset,this.get_block_or_sys_size(domain),parent_domain,null,this))
    begin
      `vmm_error(this.log,$psprintf("set_offset for %s failed",this.get_fullname()));
      return 0;
    end
    return this.Xset_base_addrX(offset,domain);
  end

  if (offset != 0) begin
     `vmm_error(this.log, $psprintf("Cannot set offset for top-level system \"%s\": must always be 0.", this.get_fullname()));
  end

  return 0;
endfunction


function bit vmm_ral_sys::Xcheck_child_overlapX(int unsigned my_offset,
                                                int unsigned my_size,
                                                string domain = "",
                                                vmm_ral_block blk,
                                                vmm_ral_sys sys);

  vmm_ral_sys subsys[];
  vmm_ral_block blks[];
  int unsigned str_addr[];
  int unsigned end_addr[];
  int unsigned my_end_addr;
  int size;
  string dm[];
  vmm_ral_sys parent_sys;
  string parent_domain;
  int j;

  Xcheck_child_overlapX = 0;
  j = this.get_domain_index(domain);
  if (j < 0)
  begin
     `vmm_warning(this.log, $psprintf("Unable to locate domain \"%s\" in system \"%s\".",
                                      domain, this.get_fullname()));
     return 0;
  end

  j =0;
  this.get_subsys(subsys,dm,domain);
  foreach(subsys[j])
  begin
    if((sys != null) && (subsys[j] == sys))
    begin
      size = my_offset - sys.get_base_addr(dm[j]);
      my_end_addr = my_offset + (my_size * (((sys.get_n_bytes(dm[j]) - 1)/this.get_n_bytes(domain))+1)) - 1;
    end
    else
    begin
      str_addr = new[str_addr.size + 1] (str_addr);
      str_addr[str_addr.size-1] = subsys[j].get_base_addr(dm[j]);
      end_addr = new[end_addr.size + 1] (end_addr);
      end_addr[end_addr.size-1] = str_addr[str_addr.size-1] + 
                                  (subsys[j].get_block_or_sys_size(dm[j]) *
                                  (((subsys[j].get_n_bytes(dm[j]) - 1)/this.get_n_bytes(domain))+1)) -1;
    end
    
  end

  j =0;
  this.get_blocks(blks,dm,domain);
  foreach(blks[j])
  begin
    if((blk != null) && (blks[j] == blk))
    begin
      size = my_offset - blk.get_base_addr(dm[j]);
      my_end_addr = my_offset + (my_size * (((blk.get_n_bytes(dm[j]) - 1)/this.get_n_bytes(domain))+1)) - 1;
    end
    else
    begin
      str_addr = new[str_addr.size + 1] (str_addr);
      str_addr[str_addr.size-1] = blks[j].get_base_addr(dm[j]);
      end_addr = new[end_addr.size + 1] (end_addr);
      end_addr[end_addr.size-1] = str_addr[str_addr.size-1] + 
                                  (blks[j].get_block_or_sys_size(dm[j]) *
                                  (((blks[j].get_n_bytes(dm[j]) - 1)/this.get_n_bytes(domain))+1)) - 1;
    end
    
  end

  j = 0;
  foreach(str_addr[j])
  begin
    if((my_offset == end_addr[j]) ||
       (my_end_addr == str_addr[j]) ||
       (my_offset == str_addr[j]) ||
       (my_end_addr == end_addr[j]))
    begin
      `vmm_warning(this.log,$psprintf("System %s has found address range conflict inbetween its child subsystems/blocks",this.get_fullname));
      return 0;
    end
    else if(my_offset < str_addr[j])
    begin
      if(my_end_addr > str_addr[j])
      begin
        `vmm_warning(this.log,$psprintf("System %s has found address range conflict inbetween its child subsystems/blocks",this.get_fullname));
        return 0;
      end
    end
    else
    begin
      if(my_offset < end_addr[j])
      begin
        `vmm_warning(this.log,$psprintf("System %s has found address range conflict inbetween its child subsystems/blocks",this.get_fullname));
        return 0;
      end
    end
  end
  Xcheck_child_overlapX = 1;

  //check if parent present for this system
  if(this.get_parent() != null)
  begin
    if(my_offset >= this.get_block_or_sys_size(domain))
      size += this.get_block_or_sys_size(domain);
    else
      size = this.get_block_or_sys_size(domain);

    parent_sys = this.get_parent();
    parent_domain = this.get_parent_domain(domain);
    Xcheck_child_overlapX =
      parent_sys.Xcheck_child_overlapX(this.get_base_addr(domain),size,parent_domain,null,this);
  end

endfunction


function vmm_ral_sys vmm_ral_get_sys_by_ID(int unsigned id);
   vmm_ral_sys sys;
   vmm_ral_block_or_sys blk_or_sys;

   blk_or_sys = vmm_ral_get_block_or_sys_by_ID(id);
   if ($cast(sys, blk_or_sys)) vmm_ral_get_sys_by_ID = sys;
   else vmm_ral_get_sys_by_ID = null;
endfunction

