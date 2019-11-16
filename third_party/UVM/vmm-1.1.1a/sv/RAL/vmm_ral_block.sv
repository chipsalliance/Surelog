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


class vmm_ral_block extends vmm_ral_block_or_sys;

   local vmm_ral_reg  regs[$];
   local vmm_ral_vreg vregs[$];
   local vmm_ral_mem  mems[$];

   extern function new(vmm_ral_sys                   parent,
                       string                        name,
                       string                        typename,
                       int unsigned                  n_bytes,
                       vmm_ral::endianness_e         endian,
                       bit [`VMM_RAL_ADDR_WIDTH-1:0] base_addr,
                       string                        domain   = "",
                       int                           cover_on = vmm_ral::NO_COVERAGE,
                       int                           has_cover = vmm_ral::NO_COVERAGE);

   /*local*/ extern virtual function void Xlock_modelX();
   /*local*/ extern function void register_reg(vmm_ral_reg register);
   /*local*/ extern function void register_vreg(vmm_ral_vreg register);
   /*local*/ extern function void register_mem(vmm_ral_mem memory);
   /*local*/ extern virtual function void Xregister_ral_accessX(vmm_ral_access access);

`ifdef VMM_RAL_FAST_SRCH
   extern local function void Xinit_reg_by_offset_mapX();
   vmm_ral_reg_by_offset_map reg_map_by_domain[*];
   extern /*local*/ function vmm_ral_reg_by_offset_map Xget_reg_by_offset_mapX(string domain); 
`endif

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
   extern virtual function vmm_ral_reg get_reg_by_offset(bit [`VMM_RAL_ADDR_WIDTH-1:0] offset,
                                                         string                        domain = "");

   extern virtual function void get_memories(ref vmm_ral_mem mems[],
                                             input string    domain = "");
   extern virtual function vmm_ral_mem get_mem_by_name(string name);
   extern virtual function vmm_ral_mem get_mem_by_offset(bit [`VMM_RAL_ADDR_WIDTH-1:0] offset,
                                                         string                        domain = "");

   extern virtual function void get_constraints(ref string names[]);

   extern virtual function void ral_power_down(bit retain = 0);
   extern virtual function void ral_power_up(string power_domains = "");
   /*local*/ bit Xis_powered_downX;
   local bit is_powered_down_with_retention;

   extern virtual function int set_cover(int is_on);

   extern virtual function void reset(string           domain = "",
                                      vmm_ral::reset_e kind   = vmm_ral::HARD);
   extern virtual function bit needs_update();

   extern virtual task update(output vmm_rw::status_e status,
                              input  vmm_ral::path_e  path = vmm_ral::DEFAULT);
   extern virtual task mirror(output vmm_rw::status_e status,
                              input  vmm_ral::check_e check = vmm_ral::QUIET,
                              input  vmm_ral::path_e  path  = vmm_ral::DEFAULT);
   
   extern virtual task readmemh(string filename);
   extern virtual task writememh(string filename);

   extern virtual /*local*/ function void XsampleX(bit [`VMM_RAL_ADDR_WIDTH-1:0] addr,
                                                   int                           domain);
   extern protected virtual function void sample(bit [`VMM_RAL_ADDR_WIDTH-1:0] addr,
                                                 int                           domain);

   extern function int unsigned get_block_ID(); 

   extern virtual function int unsigned get_block_or_sys_size(string domain = "");

   extern virtual function bit set_offset(bit [`VMM_RAL_ADDR_WIDTH-1:0] offset,
                                          string domain = "");


endclass: vmm_ral_block
   

function vmm_ral_block::new(vmm_ral_sys                   parent,
                            string                        name,
                            string                        typename,
                            int unsigned                  n_bytes,
                            vmm_ral::endianness_e         endian,
                            bit [`VMM_RAL_ADDR_WIDTH-1:0] base_addr,
                            string                        domain = "",
                            int                           cover_on  = vmm_ral::NO_COVERAGE,
                            int                           has_cover  = vmm_ral::NO_COVERAGE);
   super.new(parent, "RAL Block", name, typename,
             n_bytes, endian, base_addr, domain,
             cover_on, has_cover);
   this.Xis_powered_downX = 0;
endfunction: new


function void vmm_ral_block::Xlock_modelX();
   if (this.Xis_lockedX()) return;

   super.Xlock_modelX();
   `foreach (this.regs,i) begin
      this.regs[i].Xlock_modelX();
   end
   `foreach (this.mems,i) begin
      this.mems[i].Xlock_modelX();
   end

`ifdef VMM_RAL_FAST_SRCH
   this.Xinit_reg_by_offset_mapX();
`endif
endfunction: Xlock_modelX


`ifdef VMM_RAL_FAST_SRCH
function void vmm_ral_block::Xinit_reg_by_offset_mapX();
   string domains[];
   this.get_domains(domains);
   foreach (domains[i]) begin
      vmm_ral_reg  regs[];
      this.reg_map_by_domain[i] = new;

      this.get_registers(regs, domains[i]);
      foreach (regs[l]) begin
         bit [`VMM_RAL_ADDR_WIDTH-1:0] offset_in_blk 
            = regs[l].get_offset_in_block(domains[i]);
         this.reg_map_by_domain[i].reg_by_offset[offset_in_blk] = regs[l];
      end
   end
endfunction


function vmm_ral_reg_by_offset_map vmm_ral_block::Xget_reg_by_offset_mapX(string domain); 
   int j = this.get_domain_index(domain);
   if (j < 0) begin
      `vmm_warning(this.log, $psprintf("Unable to locate domain \"%s\" in Block \"%s\".",
                                       domain, this.get_fullname()));
      return null;
   end
   if (this.reg_map_by_domain.exists(j)) return this.reg_map_by_domain[j];
   `vmm_warning(this.log, $psprintf("Unable to locate 'reg_by_offset_map' in domain \"%s\" of Block \"%s\".",
                                     domain, this.get_fullname()));
   return null;
endfunction
`endif


function void vmm_ral_block::register_reg(vmm_ral_reg register);
   if (this.Xis_lockedX()) begin
      `vmm_error(this.log, "Cannot add register to locked block model");
      return;
   end

   // Check if this register has already been registered with this block
   `foreach (this.regs,i) begin
      if (this.regs[i] == register) begin
         `vmm_error(this.log, $psprintf("Register \"%s\" has already been registered with block \"%s\".\n",
                                       register.get_name(), this.get_name()));
         return;
      end
   end
   this.regs.push_back(register);
endfunction: register_reg

function void vmm_ral_block::register_vreg(vmm_ral_vreg register);
   if (this.Xis_lockedX()) begin
      `vmm_error(this.log, "Cannot add virtual register to locked block model");
      return;
   end

   // Check if this register has already been registered with this block
   `foreach (this.vregs,i) begin
      if (this.vregs[i] == register) begin
         `vmm_error(this.log, $psprintf("Virtual register \"%s\" has already been registered with block \"%s\".\n",
                                       register.get_name(), this.get_name()));
         return;
      end
   end
   this.vregs.push_back(register);
endfunction: register_vreg

function void vmm_ral_block::register_mem(vmm_ral_mem memory);
   if (this.Xis_lockedX()) begin
      `vmm_error(this.log, "Cannot add memory to locked block model");
      return;
   end

   // Check if this memory has already been registered with this block
   `foreach (this.mems,i) begin
      if (this.mems[i] == memory) begin
         `vmm_error(this.log, $psprintf("Memory \"%s\" has already been registered with block \"%s\".\n",
                                       memory.get_name(), this.get_name()));
         return;
      end
   end
   this.mems.push_back(memory);
endfunction: register_mem


function void vmm_ral_block::Xregister_ral_accessX(vmm_ral_access access);
   // There can only be one RAL Access on a RAL model
   if (this.ral_access != null && this.ral_access != access) begin
      `vmm_fatal(this.log, $psprintf("Block %s is already used by another RAL access instance", this.get_fullname()));
   end
   this.ral_access = access;

   // Register all sub-elements
   begin
      vmm_ral_reg  regs[];
      vmm_ral_mem  mems[];

      this.get_registers(regs);
      foreach (regs[i]) begin
         regs[i].Xregister_ral_accessX(access);
      end

      this.get_memories(mems);
      foreach (mems[i]) begin
         mems[i].Xregister_ral_accessX(access);
      end
   end
endfunction: Xregister_ral_accessX


function string vmm_ral_block::psdisplay(string prefix = "",
                                         string domain = "");
   string       domains[];
   vmm_ral_reg  regs[];
   vmm_ral_vreg vregs[];
   vmm_ral_mem  mems[];
   bit          single_domain;
   vmm_ral::endianness_e endian;

   single_domain = 1;
   if (domain == "") begin
      this.get_domains(domains);
      if (domains.size() > 1) single_domain = 0;
   end
   if (single_domain) begin
      $sformat(psdisplay, "%sBlock %s", prefix, this.get_fullname());
      if (domain != "") $sformat(psdisplay, "%s.%s", psdisplay, domain);
      endian = this.get_endian(domain);
      $sformat(psdisplay, "%s -- %0d bytes (%s)", psdisplay,
               this.get_n_bytes(domain), endian.name());
      this.get_registers(regs, domain);
      foreach (regs[j]) begin
         $sformat(psdisplay, "%s\n%s", psdisplay,
                  regs[j].psdisplay({prefix, "   "}, domain));
      end
      this.get_virtual_registers(vregs, domain);
      foreach (vregs[j]) begin
         $sformat(psdisplay, "%s\n%s", psdisplay,
                  vregs[j].psdisplay({prefix, "   "}, domain));
      end
      this.get_memories(mems, domain);
      foreach (mems[j]) begin
         $sformat(psdisplay, "%s\n%s", psdisplay,
                  mems[j].psdisplay({prefix, "   "}, domain));
      end
   end
   else begin
      $sformat(psdisplay, "%sBlock %s", prefix, this.get_fullname());
      foreach (domains[i]) begin
         endian = this.get_endian(domains[i]);
         $sformat(psdisplay, "%s\n%s   Domain \"%s\" -- %0d bytes (%s)",
                  psdisplay, prefix, domains[i],
                  this.get_n_bytes(domains[i]), endian.name());
         this.get_registers(regs, domains[i]);
         foreach (regs[j]) begin
            $sformat(psdisplay, "%s\n%s", psdisplay,
                     regs[j].psdisplay({prefix, "      "},
                                       domains[i]));
         end
         this.get_virtual_registers(vregs, domains[i]);
         foreach (vregs[j]) begin
            $sformat(psdisplay, "%s\n%s", psdisplay,
                     vregs[j].psdisplay({prefix, "      "},
                                       domains[i]));
         end
         this.get_memories(mems, domains[i]);
         foreach (mems[j]) begin
            $sformat(psdisplay, "%s\n%s", psdisplay,
                     mems[j].psdisplay({prefix, "      "}, domains[i]));
         end
      end
   end
endfunction: psdisplay


function void vmm_ral_block::get_fields(ref vmm_ral_field fields[],
                                        input string      domain = "");
   int n;
   vmm_ral_reg r[];
   vmm_ral_field f[];

   fields = new [0];
   this.get_registers(r, domain);
   foreach (r[i]) begin
      r[i].get_fields(f);
      n = fields.size();
      fields = new [n + f.size()] (fields);

      foreach (f[j]) begin
         fields[n++] = f[j];
      end
   end
endfunction: get_fields

function void vmm_ral_block::get_virtual_fields(ref vmm_ral_vfield fields[],
                                                input string      domain = "");
   int n;
   vmm_ral_vreg r[];
   vmm_ral_vfield f[];

   fields = new [0];
   this.get_virtual_registers(r, domain);
   foreach (r[i]) begin
      r[i].get_fields(f);
      n = fields.size();
      fields = new [n + f.size()] (fields);

      foreach (f[j]) begin
         fields[n++] = f[j];
      end
   end
endfunction: get_virtual_fields

function vmm_ral_field vmm_ral_block::get_field_by_name(string name);
   // Search the registers to find the first field of the specified name
   `foreach (this.regs,i) begin
      vmm_ral_field fields[];
      this.regs[i].get_fields(fields);
      foreach (fields[j]) begin
         if (fields[j].get_name() == name) begin
            return fields[j];
         end
      end
   end
   `vmm_warning(this.log, $psprintf("Unable to locate field \"%s\" in block \"%s\".",
                                    name, this.get_fullname()));
   get_field_by_name = null;
endfunction: get_field_by_name

function vmm_ral_vfield vmm_ral_block::get_virtual_field_by_name(string name);
   // Search the registers to find the first field of the specified name
   `foreach (this.vregs,i) begin
      vmm_ral_vfield fields[];
      this.vregs[i].get_fields(fields);
      foreach (fields[j]) begin
         if (fields[j].get_name() == name) begin
            return fields[j];
         end
      end
   end
   `vmm_warning(this.log, $psprintf("Unable to locate virtual field \"%s\" in block \"%s\".",
                                    name, this.get_fullname()));
   get_virtual_field_by_name = null;
endfunction: get_virtual_field_by_name


function void vmm_ral_block::get_registers(ref vmm_ral_reg regs[],
                                           input string    domain = "");
   if (domain == "") begin
      regs = new [this.regs.size()];
      `foreach(this.regs,i) begin
         regs[i] = this.regs[i];
      end
   end
   else begin
      int n = 0;
      regs = new [this.regs.size()];
      `foreach(this.regs,i) begin
         // Is the register in the specified domain?
         string domains[];
         this.regs[i].get_domains(domains);
         foreach(domains[j]) begin
            if (domains[j] == domain) begin
               regs[n++] = this.regs[i];
               break;
            end
         end
      end
      regs = new [n] (regs);
   end
endfunction: get_registers

function void vmm_ral_block::get_virtual_registers(ref vmm_ral_vreg vregs[],
                                                   input string    domain = "");
   if (domain == "") begin
      vregs = new [this.vregs.size()];
      `foreach(this.vregs,i) begin
         vregs[i] = this.vregs[i];
      end
   end
   else begin
      int n = 0;
      vregs = new [this.vregs.size()];
      `foreach(this.vregs,i) begin
         // Is the register in the specified domain?
         string domains[];
         if(this.vregs[i].get_memory() != null)
         begin
           this.vregs[i].get_domains(domains);
           foreach(domains[j]) begin
              if (domains[j] == domain) begin
                 vregs[n++] = this.vregs[i];
                 break;
              end
           end
         end
      end
      vregs = new [n] (vregs);
   end
endfunction: get_virtual_registers

function vmm_ral_reg vmm_ral_block::get_reg_by_name(string name);
   `foreach (this.regs,i) begin
      if (this.regs[i].get_name() == name) begin
         return this.regs[i];
      end
   end
   `vmm_warning(this.log, $psprintf("Unable to locate register \"%s\" in block \"%s\".",
                                    name, this.get_fullname()));
   get_reg_by_name = null;
endfunction: get_reg_by_name

function vmm_ral_vreg vmm_ral_block::get_vreg_by_name(string name);
   `foreach (this.vregs,i) begin
      if (this.vregs[i].get_name() == name) begin
         return this.vregs[i];
      end
   end
   `vmm_warning(this.log, $psprintf("Unable to locate virtual register \"%s\" in block \"%s\".",
                                    name, this.get_fullname()));
   get_vreg_by_name = null;
endfunction: get_vreg_by_name

function vmm_ral_reg vmm_ral_block::get_reg_by_offset(bit [`VMM_RAL_ADDR_WIDTH-1:0] offset,
                                                      string                        domain = "");
   vmm_ral_reg regs[];

   this.get_registers(regs, domain);
   foreach (regs[i]) begin
      if (regs[i].get_offset_in_block(domain) == offset) begin
         return regs[i];
      end
   end
   `vmm_warning(this.log, $psprintf("Unable to locate register at offset 0x%h %0sin block \"%s\".",
                                    offset, ((domain == "") ? "" : $psprintf("in domain \"%s\" ",
                                                                             domain)),
                                    this.get_fullname()));
   get_reg_by_offset = null;
endfunction: get_reg_by_offset


function void vmm_ral_block::get_memories(ref vmm_ral_mem mems[],
                                          input string    domain = "");
   if (domain == "") begin
      mems = new [this.mems.size()];
      `foreach(this.mems,i) begin
         mems[i] = this.mems[i];
      end
   end
   else begin
      int n = 0;
      mems = new [this.mems.size()];
      `foreach(this.mems,i) begin
         // Is the memory in the specified domain?
         string domains[];
         this.mems[i].get_domains(domains);
         foreach(domains[j]) begin
            if (domains[j] == domain) begin
               mems[n++] = this.mems[i];
               break;
            end
         end
      end
      mems = new [n] (mems);
   end
endfunction: get_memories


function vmm_ral_mem vmm_ral_block::get_mem_by_name(string name);
   `foreach (this.mems,i) begin
      if (this.mems[i].get_name() == name) begin
         return this.mems[i];
      end
   end
   `vmm_warning(this.log, $psprintf("Unable to locate memory \"%s\" in block \"%s\".",
                                    name, this.get_fullname()));
   get_mem_by_name = null;
endfunction: get_mem_by_name


function vmm_ral_mem vmm_ral_block::get_mem_by_offset(bit [`VMM_RAL_ADDR_WIDTH-1:0] offset,
                                                      string                        domain ="");
   //get_mem_by_offset = this.mems.first() with index: (this.mems[index].offset_in_block == offset);
endfunction: get_mem_by_offset


function void vmm_ral_block::get_constraints(ref string names[]);
endfunction: get_constraints


function void vmm_ral_block::ral_power_down(bit retain = 0);
   vmm_ral_mem mems[];

   if (this.Xis_powered_downX) begin
      // It's OK to insist that the block is powered down, but
      // you can't get state retention if it was previously powered down without it
      if (!this.is_powered_down_with_retention && retain) begin
         `vmm_error(this.log, $psprintf("Cannot power-down memory \"%s\" with retention because is has already been powered down without retention",
                                        this.get_fullname()));
         return;
      end
   end

   // Power down all memories
   this.get_memories(mems);
   foreach (mems[i]) begin
      mems[i].ral_power_down();
   end

   this.Xis_powered_downX = 1;
   this.is_powered_down_with_retention = retain;
endfunction: ral_power_down


function void vmm_ral_block::ral_power_up(string power_domains = "");
   vmm_ral_reg  regs[];
   vmm_ral_mem  mems[];
   string       pwr_domain;

   if (power_domains != "") begin
      pwr_domain = this.get_attribute("POWER_DOMAIN");
      if (!`vmm_str_match(pwr_domain, power_domains)) return;
   end

   // Initialize registers based on powered-down retention
   this.get_registers(regs);
   foreach (regs[i]) begin
      if (!this.is_powered_down_with_retention) regs[i].reset();
      else begin
         string retain_attrib = regs[i].get_attribute("RETAIN");
         if (retain_attrib == "" ||
             retain_attrib == "0") regs[i].reset();
      end
   end

   // Power up memories in the specified power domains
   this.get_memories(mems);
   foreach (mems[i]) begin
      if (power_domains != "") begin
         pwr_domain = mems[i].get_attribute("POWER_DOMAIN");
         if (!`vmm_str_match(pwr_domain, power_domains)) continue;
      end
      mems[i].ral_power_up();
   end
   
   this.Xis_powered_downX = 0;
endfunction: ral_power_up


function int vmm_ral_block::set_cover(int is_on);
   int can_cvr;

   set_cover = super.set_cover(is_on);
   can_cvr = is_on & set_cover;
   if (can_cvr == 0) return set_cover;

   `foreach (this.regs,i) begin
      void'(this.regs[i].set_cover(can_cvr));
   end
   `foreach (this.mems,i) begin
      void'(this.mems[i].set_cover(can_cvr));
   end
endfunction: set_cover


function void vmm_ral_block::reset(string           domain = "",
                                   vmm_ral::reset_e kind = vmm_ral::HARD);
   vmm_ral_reg regs[];
   vmm_ral_mem mems[];

   this.get_registers(regs, domain);
   foreach (regs[i]) begin
      regs[i].reset(kind);
   end

   this.get_memories(mems, domain);
   foreach (mems[i]) begin
      vmm_ral_vreg vregs[];
      mems[i].get_virtual_registers(vregs);
      foreach (vregs[j]) begin
         vregs[j].reset(kind);
      end
   end
endfunction: reset


function bit vmm_ral_block::needs_update();
   needs_update = 0;
   `foreach (this.regs,i) begin
      if (this.regs[i].needs_update()) begin
         return 1;
      end
   end
endfunction: needs_update


task vmm_ral_block::update(output vmm_rw::status_e status,
                           input  vmm_ral::path_e  path = vmm_ral::DEFAULT);
   string domains[];
   bit    updated;

   status = vmm_rw::IS_OK;
   `foreach (this.regs,i) begin
      if (!this.regs[i].needs_update()) continue;

      this.regs[i].get_domains(domains);

      if (path == vmm_ral::BACKDOOR) begin
         this.regs[i].update(status, path, domains[0]);
         if (status == vmm_rw::IS_OK) continue;
         `vmm_error(this.log, $psprintf("Register \"%s\" could not be updated",
                                        regs[i].get_fullname()));
         return;
      end

      // Find the first writeable domain to
      // perform the update through
      updated = 0;
      foreach (domains[j]) begin
         if (this.regs[i].get_rights(domains[j]) != vmm_ral::RO) begin
            this.regs[i].update(status, path, domains[j]);
            if (status == vmm_rw::IS_OK) begin
               updated = 1;
               break;
            end
         end
      end
      if (!updated) begin
         `vmm_error(this.log, $psprintf("Register \"%s\" could not be updated",
                                        regs[i].get_fullname()));
         if (status == vmm_rw::IS_OK) status = vmm_rw::ERROR;
         return;
      end
   end
endtask: update


task vmm_ral_block::mirror(output vmm_rw::status_e status,
                           input  vmm_ral::check_e check = vmm_ral::QUIET,
                           input  vmm_ral::path_e  path = vmm_ral::DEFAULT);
   string domains[];
   bit mirrored;

   status = vmm_rw::IS_OK;
   `foreach (this.regs,i) begin

      if (path == vmm_ral::BACKDOOR) begin
         this.regs[i].mirror(status, check, path);
         if (status != vmm_rw::IS_OK) return;
         continue;
      end

      // Find the first readable domain to
      // perform the update through
      this.regs[i].get_domains(domains);
      mirrored = 0;
      foreach (domains[j]) begin
         if (this.regs[i].get_rights(domains[j]) != vmm_ral::WO) begin
            this.regs[i].mirror(status, check, path, domains[0]);
            if (status == vmm_rw::IS_OK) begin
               mirrored = 1;
               break;
            end
         end
      end
      if (!mirrored) begin
         `vmm_error(this.log, $psprintf("Register \"%s\" could not be mirrored",
                                        regs[i].get_fullname()));
         if (status == vmm_rw::IS_OK) status = vmm_rw::ERROR;
         return;
      end
   end
endtask: mirror


task vmm_ral_block::readmemh(string filename);
endtask: readmemh


task vmm_ral_block::writememh(string filename);
endtask: writememh


function void vmm_ral_block::XsampleX(bit [`VMM_RAL_ADDR_WIDTH-1:0] addr,
                                      int                           domain);
   this.sample(addr, domain);
endfunction


function void vmm_ral_block::sample(bit [`VMM_RAL_ADDR_WIDTH-1:0] addr,
                                    int                           domain);
   // Nothing to do in this base class
endfunction


function bit vmm_ral_block::set_offset(bit [`VMM_RAL_ADDR_WIDTH-1:0] offset,
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
    if(!parent_sys.Xcheck_child_overlapX(offset,this.get_block_or_sys_size(domain),parent_domain,this,null))
    begin
     `vmm_error(this.log,$psprintf("set_offset for %s failed",this.get_fullname()));
      return 0;
    end
    return this.Xset_base_addrX(offset,domain);
  end

  if (offset != 0) begin
    `vmm_error(this.log, $psprintf("Cannot set offset for top-level block \"%s\": must always be 0.",
                                   this.get_fullname()));
  end

  return 0;
endfunction


function int unsigned vmm_ral_block::get_block_or_sys_size(string domain = "");

  vmm_ral_reg regs[];
  vmm_ral_mem mems[];
  int j;
  int unsigned max_addr = 0;
  int unsigned size     = 1;

  j = this.get_domain_index(domain);
  if (j < 0)
  begin
     `vmm_warning(this.log, $psprintf("Unable to locate domain \"%s\" in Block \"%s\".",
                                      domain, this.get_fullname()));
     get_block_or_sys_size = 0;
     return 0;
  end


  this.get_registers(regs,domain);
  this.get_memories(mems,domain);

  foreach (regs[i])
  begin
    int unsigned offset_blk;
    offset_blk = regs[i].get_offset_in_block(domain);
    if (offset_blk > max_addr)
    begin
      max_addr = offset_blk + ((regs[i].get_n_bytes()-1)/this.get_n_bytes(domain));
    end
  end

  foreach (mems[i])
  begin
    int unsigned offset_blk;
    offset_blk = mems[i].get_offset_in_block(0,domain);
    if (offset_blk > max_addr)
    begin
      max_addr = offset_blk + (mems[i].get_size() * (((mems[i].get_n_bytes()-1)/this.get_n_bytes(domain))+1)) -1;
    end
  end

  get_block_or_sys_size = max_addr + 1;

endfunction : get_block_or_sys_size

function int unsigned vmm_ral_block::get_block_ID(); 
   get_block_ID =  this.get_block_or_sys_ID();
endfunction

function vmm_ral_block vmm_ral_get_block_by_ID(int unsigned id);
   vmm_ral_block blk;
   vmm_ral_block_or_sys blk_or_sys;

   blk_or_sys = vmm_ral_get_block_or_sys_by_ID(id);
   if ($cast(blk, blk_or_sys)) vmm_ral_get_block_by_ID = blk;
   else vmm_ral_get_block_by_ID = null;
endfunction

