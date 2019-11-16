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

`ifdef VMM_RAL_FAST_SRCH
class vmm_ral_reg_by_offset_map;
   vmm_ral_reg reg_by_offset[*];
endclass : vmm_ral_reg_by_offset_map
`endif


virtual class vmm_ral_block_or_sys;
   static vmm_log log = new("RAL", "Block/Sys"); 

   vmm_ral::path_e default_access = vmm_ral::DEFAULT;

   static local int unsigned block_or_sys_id_factory = 0;
   static vmm_ral_block_or_sys all_blocks_and_systems[*];
   local int unsigned block_or_sys_id = 0;

   local bit locked;

   local string name;
   local string typename;

   protected string                    domains[];
   local string                        in_domains[]; // For each domain
   local int unsigned                  n_bytes[];    // For each domain
   local vmm_ral::endianness_e         endian[];     // For each domain
   local bit [`VMM_RAL_ADDR_WIDTH-1:0] base_addr[];  // For each domain
   local string                        constr[];     // Constraint blocks

   local vmm_ral_sys parent;
   protected vmm_ral_access ral_access;

   local string attributes[string];

   local int has_cover;
   local int cover_on;

   extern function new(vmm_ral_sys                   parent,
                       string                        block_or_sys,
                       string                        name,
                       string                        typename,
                       int unsigned                  n_bytes,
                       vmm_ral::endianness_e         endian,
                       bit [`VMM_RAL_ADDR_WIDTH-1:0] base_addr,
                       string                        domain = "",
                       int                           cover_on = vmm_ral::NO_COVERAGE,
                       int                           has_cover = vmm_ral::NO_COVERAGE);

   /*local*/ extern virtual function void Xlock_modelX();
   /*local*/ extern function bit Xis_lockedX();
   /*local*/ extern virtual function void add_domain(int unsigned          n_bytes,
                                                     vmm_ral::endianness_e endian,
                                                     string                domain);
   /*local*/ extern virtual function void map_domain(string                        domain,
                                                     string                        in_domain,
                                                     bit [`VMM_RAL_ADDR_WIDTH-1:0] base_addr);
   /*local*/ extern virtual function void Xregister_ral_accessX(vmm_ral_access access);
   /*local*/ extern function void Xadd_constraintsX(string name);
   
   extern virtual function string get_name();
   extern virtual function string get_type();
   extern virtual function string get_fullname();
   extern function void get_domains(ref string names[]);
   extern virtual function vmm_ral_sys get_parent();
   extern virtual function bit [`VMM_RAL_ADDR_WIDTH-1:0] get_base_addr(string domain = "");
   extern         function int C_addr_of();
   extern virtual function int unsigned get_n_bytes(string domain = "");
   extern virtual function vmm_ral::endianness_e get_endian(string domain = "");
   extern virtual function vmm_ral::path_e get_default_access();
   extern virtual function string get_parent_domain(string domain = "");
   extern virtual function string get_external_domain(string domain = "");

   extern virtual function void display(string prefix = "",
                                        string domain = "");
   extern virtual function string psdisplay(string prefix = "",
                                            string domain = "");

   extern virtual function void get_fields(ref vmm_ral_field fields[],
                                           input string      domain = ""); 
   extern virtual function vmm_ral_field get_field_by_name(string name);

   extern virtual function void get_registers(ref vmm_ral_reg regs[],
                                              input string    domain = "");
   extern virtual function void get_virtual_registers(ref vmm_ral_vreg vregs[],
                                                      input string    domain = "");
   extern virtual function vmm_ral_reg get_reg_by_name(string name);
   extern virtual function vmm_ral_reg get_reg_by_offset(bit [`VMM_RAL_ADDR_WIDTH-1:0] offset,
                                                         string                        domain = "");

   extern virtual function void get_memories(ref vmm_ral_mem mems[],
                                             input string    domain = "");
   extern virtual function vmm_ral_mem get_mem_by_name(string name);
   extern virtual function vmm_ral_mem get_mem_by_offset(bit [`VMM_RAL_ADDR_WIDTH-1:0] offset,
                                                         string                        domain = "");

   extern virtual function void get_constraints(ref string names[]);

   extern virtual function void set_attribute(string name,
                                              string value);
   extern virtual function string get_attribute(string name,
                                                bit inherited = 1);
   extern virtual function void get_all_attributes(ref string names[],
                                                   input bit inherited = 1);

   extern virtual function void ral_power_down(bit retain = 0);
   extern virtual function void ral_power_up(string power_domains = "");

   extern virtual function bit can_cover(int models);
   extern virtual function int set_cover(int is_on);
   extern virtual function bit is_cover_on(int is_on = vmm_ral::ALL_COVERAGE);

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

   extern function void prepend_callback(vmm_ral_callbacks cbs);
   extern function void append_callback(vmm_ral_callbacks cbs);
   extern function void unregister_callback(vmm_ral_callbacks cbs);

   extern protected function int get_domain_index(string domain);

   extern function int unsigned get_block_or_sys_ID();

   extern virtual function int unsigned get_block_or_sys_size(string domain = "");

   extern virtual function bit set_offset(bit [`VMM_RAL_ADDR_WIDTH-1:0] offset,
                                          string domain = "");

   extern virtual function bit Xcheck_child_overlapX(int unsigned my_offset,
                                                     int unsigned my_size,
                                                     string domain = "",
                                                     vmm_ral_block blk,
                                                     vmm_ral_sys sys);

   extern virtual function bit Xset_base_addrX(bit [`VMM_RAL_ADDR_WIDTH-1:0] offset, 
                                               string domain = "");

   protected virtual function void domain_coverage(string domain,
                                               int    idx);
   endfunction
endclass: vmm_ral_block_or_sys
   

function vmm_ral_block_or_sys::new(vmm_ral_sys                   parent,
                                   string                        block_or_sys,
                                   string                        name,
                                   string                        typename,
                                   int unsigned                  n_bytes,
                                   vmm_ral::endianness_e         endian,
                                   bit [`VMM_RAL_ADDR_WIDTH-1:0] base_addr,
                                   string                        domain = "",
                                   int                           cover_on = vmm_ral::NO_COVERAGE,
                                   int                           has_cover = vmm_ral::NO_COVERAGE);
   this.locked = 0;

   this.name = name;
   this.typename = typename;
   begin
      vmm_ral_block_or_sys p = parent;
      if (p == this) parent = null;
   end
   this.parent = parent;

   this.domains   = new [1]; this.domains[0]   = domain;
   this.in_domains= new [1]; this.in_domains[0]= "";
   this.n_bytes   = new [1]; this.n_bytes[0]   = n_bytes;
   this.endian    = new [1]; this.endian[0]    = endian;
   this.base_addr = new [1]; this.base_addr[0] = base_addr;

   this.has_cover = has_cover;
   this.cover_on = vmm_ral::NO_COVERAGE;
   void'(this.set_cover(cover_on));

   this.block_or_sys_id = ++this.block_or_sys_id_factory;
   all_blocks_and_systems[this.block_or_sys_id] = this;
   this.domain_coverage(domain, 0);
endfunction: new

function void vmm_ral_block_or_sys::Xlock_modelX();
   this.locked = 1;
endfunction: Xlock_modelX


function bit vmm_ral_block_or_sys::Xis_lockedX();
   Xis_lockedX = this.locked;
endfunction: Xis_lockedX


function void vmm_ral_block_or_sys::add_domain(int unsigned          n_bytes,
                                               vmm_ral::endianness_e endian,
                                               string                domain);
   int n;

   if (this.locked) begin
      `vmm_error(this.log, "Cannot add domain to locked model");
      return;
   end

   n = this.domains.size();
   this.domains   = new [n+1] (this.domains);   this.domains[n]   = domain;
   this.in_domains= new [n+1] (this.in_domains);this.in_domains[n]= "";
   this.n_bytes   = new [n+1] (this.n_bytes);   this.n_bytes[n]   = n_bytes;
   this.endian    = new [n+1] (this.endian);    this.endian[n]    = endian;
   this.base_addr = new [n+1] (this.base_addr); this.base_addr[n] = 0;
   this.domain_coverage(domain, n);
endfunction: add_domain


function void vmm_ral_block_or_sys::map_domain(string                        domain,
                                               string                        in_domain,
                                               bit [`VMM_RAL_ADDR_WIDTH-1:0] base_addr);
   int n;

   n = this.get_domain_index(domain);
   if (n < 0) return;

   if (this.in_domains[n] != "") begin
      `vmm_error(this.log, $psprintf("Domain \"%s\" already mapped in domain \"%s\" @'h%h in %s",
                                     domain, in_domains[n], base_addr[n],
                                     this.get_fullname()));
      return;
   end

   this.in_domains[n] = in_domain;
   this.base_addr[n]  = base_addr;
endfunction: map_domain


function void vmm_ral_block_or_sys::Xregister_ral_accessX(vmm_ral_access access);
endfunction

function void vmm_ral_block_or_sys::Xadd_constraintsX(string name);
   int n;

   if (this.locked) begin
      `vmm_error(this.log, "Cannot add constraints to locked model");
      return;
   end

   // Check if the constraint block already exists
   `foreach (this.constr,i) begin
      if (this.constr[i] == name) begin
         `vmm_warning(this.log, $psprintf("Constraint \"%s\" already added",
                                          name));
         return;
      end
   end

   // Append the constraint name to the list
   n = this.constr.size();
   this.constr = new [n+1] (this.constr);
   this.constr[n] = name;
endfunction: Xadd_constraintsX


function string vmm_ral_block_or_sys::get_name();
   get_name = this.name;
endfunction: get_name


function string vmm_ral_block_or_sys::get_type();
   return this.typename;
endfunction: get_type


function string vmm_ral_block_or_sys::get_fullname();
   vmm_ral_block_or_sys bos;

   get_fullname = this.get_name();

   // Do not include top-level name in full name
   bos = this.get_parent();
   if (bos == null) return get_fullname;
   if (bos.get_parent() == null) return get_fullname;

   get_fullname = {this.parent.get_fullname(), ".", get_fullname};
endfunction: get_fullname


function void vmm_ral_block_or_sys::get_domains(ref string names[]);
   names = new [this.domains.size()] (this.domains);
endfunction: get_domains


function vmm_ral_sys vmm_ral_block_or_sys::get_parent();
   get_parent = this.parent;
endfunction: get_parent

function bit vmm_ral_block_or_sys::Xset_base_addrX(bit [`VMM_RAL_ADDR_WIDTH-1:0] offset, 
                                                   string domain = "");
  int i;

  i = this.get_domain_index(domain);
  if (i < 0)
  begin
    return 0;
  end
  this.base_addr[i] = offset;
  Xset_base_addrX = 1;

endfunction                                                   

function bit [`VMM_RAL_ADDR_WIDTH-1:0] vmm_ral_block_or_sys::get_base_addr(string domain = "");
   int i;

   i = this.get_domain_index(domain);
   if (i < 0) return 0;
   get_base_addr = this.base_addr[i];
endfunction: get_base_addr


function int vmm_ral_block_or_sys::C_addr_of();
   return this.get_block_or_sys_ID();
endfunction


function int unsigned vmm_ral_block_or_sys::get_n_bytes(string domain = "");
   int i;

   i = this.get_domain_index(domain);
   if (i < 0) return 0;
   get_n_bytes = this.n_bytes[i];
endfunction: get_n_bytes


function vmm_ral::endianness_e vmm_ral_block_or_sys::get_endian(string domain = "");
   int i;

   i = this.get_domain_index(domain);
   if (i < 0) return vmm_ral::LITTLE_ENDIAN;
   get_endian = this.endian[i];
endfunction: get_endian


function vmm_ral::path_e vmm_ral_block_or_sys::get_default_access();
   if (this.default_access != vmm_ral::DEFAULT) begin
      return this.default_access;
   end

   if (this.parent != null) begin
      return this.parent.get_default_access();
   end

   // Default access is defined by RAL access
   if (this.ral_access != null) begin
      get_default_access = this.ral_access.default_path;
   end
   else begin
      `vmm_fatal(log, $psprintf("RAL model for \"%s\" is not associated with a RAL access interface", this.get_fullname()));
      get_default_access = vmm_ral::BFM;
   end

   if (get_default_access == vmm_ral::DEFAULT) begin
      // Front door by default
      get_default_access = vmm_ral::BFM;
   end
endfunction: get_default_access


function string vmm_ral_block_or_sys::get_parent_domain(string domain = "");
   int i;

   // if this is the top-most block or system, there is no parent!
   if (this.parent == null) return domain;

   i = this.get_domain_index(domain);
   if (i < 0) return domain;

   return this.in_domains[i];
endfunction: get_parent_domain


function string vmm_ral_block_or_sys::get_external_domain(string domain = "");
   int i;

   // if this is the top-most block or system, there is no parent!
   if (this.parent == null) return domain;

   i = this.get_domain_index(domain);
   if (i < 0) return domain;
   return this.parent.get_external_domain(this.in_domains[i]);
endfunction: get_external_domain


function void vmm_ral_block_or_sys::display(string prefix = "",
                                            string domain = "");
   $write("%s\n", this.psdisplay(prefix, domain));
endfunction: display


function string vmm_ral_block_or_sys::psdisplay(string prefix = "",
                                                string domain = "");
  return "";
endfunction


function void vmm_ral_block_or_sys::get_fields(ref vmm_ral_field fields[],
                                               input string      domain = ""); 
endfunction


function vmm_ral_field vmm_ral_block_or_sys::get_field_by_name(string name);
endfunction

function void vmm_ral_block_or_sys::get_registers(ref vmm_ral_reg regs[],
                                                  input string    domain = "");
endfunction


function void vmm_ral_block_or_sys::get_virtual_registers(ref vmm_ral_vreg vregs[],
                                                          input string    domain = "");
endfunction


function vmm_ral_reg vmm_ral_block_or_sys::get_reg_by_name(string name);
endfunction

function vmm_ral_reg vmm_ral_block_or_sys::get_reg_by_offset(bit [`VMM_RAL_ADDR_WIDTH-1:0] offset,
                                                             string                        domain = "");
endfunction

function void vmm_ral_block_or_sys::get_memories(ref vmm_ral_mem mems[],
                                                 input string    domain = "");
endfunction


function vmm_ral_mem vmm_ral_block_or_sys::get_mem_by_name(string name);
endfunction

function vmm_ral_mem vmm_ral_block_or_sys::get_mem_by_offset(bit [`VMM_RAL_ADDR_WIDTH-1:0] offset,
                                                            string                        domain = "");
endfunction

function void vmm_ral_block_or_sys::get_constraints(ref string names[]);
   names = new [this.constr.size()] (this.constr);
endfunction: get_constraints


function void vmm_ral_block_or_sys::set_attribute(string name,
                                         string value);
   string whatami;
   vmm_ral_block blk;
   
   if ($cast(blk, this)) whatami = "block";
   else	whatami = "system";

   if (name == "") begin
      `vmm_error(this.log, $psprintf("Cannot set anonymous attribute \"\" in %s \"%s\". Please specify an attribute name.",
                                       name, whatami, this.get_fullname()));
      return;
   end

   if (this.attributes.exists(name)) begin
      if (value != "") begin
         `vmm_warning(this.log, $psprintf("Redefining attributed \"%s\" in %s \"%s\" to \"%s\".",
                                          name, whatami, this.get_fullname(), value));
         this.attributes[name] = value;
      end
      else begin
         this.attributes.delete(name);
      end
      return;
   end

   if (value == "") begin
      `vmm_warning(this.log, $psprintf("Attempting to delete non-existent attribute \"%s\" in %s \"%s\".",
                                       name, whatami, this.get_fullname()));
      return;
   end

   this.attributes[name] = value;
endfunction: set_attribute


function string vmm_ral_block_or_sys::get_attribute(string name,
                                                    bit inherited = 1);
   if (this.attributes.exists(name)) begin
      return this.attributes[name];
   end

   if (inherited && this.parent != null) return this.parent.get_attribute(name);

   return "";
endfunction: get_attribute


function void vmm_ral_block_or_sys::get_all_attributes(ref string names[],
                                                       input bit inherited = 1);
   string tmp[];
   string name;
   bit    ok;
   int    i;

   if (inherited && this.parent != null) this.parent.get_all_attributes(tmp);

   i = tmp.size();
   tmp = new [tmp.size() + this.attributes.num()] (tmp);

   ok = this.attributes.first(name);
   while (ok) begin
      int found = 0;
      foreach (tmp[j]) begin
         if (tmp[j] == name) begin
            found = 1;
            break;
         end
      end
      if (!found) tmp[i++] = name;
      ok = this.attributes.next(name);
   end
   names = new [i] (tmp);
endfunction: get_all_attributes


function void vmm_ral_block_or_sys::ral_power_down(bit retain = 0);
endfunction: ral_power_down


function void vmm_ral_block_or_sys::ral_power_up(string power_domains = "");
endfunction: ral_power_up


function bit vmm_ral_block_or_sys::can_cover(int models);
   return ((this.has_cover & models) == models);
endfunction: can_cover

function int vmm_ral_block_or_sys::set_cover(int is_on);
   if (is_on == vmm_ral::NO_COVERAGE) begin
      this.cover_on = is_on;
      return this.cover_on;
   end

   if ((this.has_cover & is_on) == 0) begin
      `vmm_warning(this.log, $psprintf("\"%s\" - Cannot turn ON any coverage becasue the corresponding coverage model was not generated.", this.get_fullname()));
      return this.cover_on;
   end

   if (is_on & vmm_ral::REG_BITS) begin
      if (this.has_cover & vmm_ral::REG_BITS) begin
          this.cover_on |= vmm_ral::REG_BITS;
      end else begin
          `vmm_warning(this.log, $psprintf("\"%s\" - Cannot turn ON Register Bit coverage becasue the corresponding coverage model was not generated.", this.get_fullname()));
      end
   end

   if (is_on & vmm_ral::FIELD_VALS) begin
      if (this.has_cover & vmm_ral::FIELD_VALS) begin
          this.cover_on |= vmm_ral::FIELD_VALS;
      end else begin
          `vmm_warning(this.log, $psprintf("\"%s\" - Cannot turn ON Field Value coverage becasue the corresponding coverage model was not generated.", this.get_fullname()));
      end
   end

   if (is_on & vmm_ral::ADDR_MAP) begin
      if (this.has_cover & vmm_ral::ADDR_MAP) begin
          this.cover_on |= vmm_ral::ADDR_MAP;
      end else begin
          `vmm_warning(this.log, $psprintf("\"%s\" - Cannot turn ON Address Map coverage becasue the corresponding coverage model was not generated.", this.get_fullname()));
      end
   end

   set_cover = this.cover_on;
endfunction: set_cover


function bit vmm_ral_block_or_sys::is_cover_on(int is_on = vmm_ral::ALL_COVERAGE);
   if (this.can_cover(is_on) == 0) return 0;
   return ((this.cover_on & is_on) == is_on);
endfunction: is_cover_on


function void vmm_ral_block_or_sys::reset(string           domain = "",
                                          vmm_ral::reset_e kind   = vmm_ral::HARD);
endfunction

function bit vmm_ral_block_or_sys::needs_update();
  return 0;
endfunction


task vmm_ral_block_or_sys::update(output vmm_rw::status_e status,
                                  input  vmm_ral::path_e  path = vmm_ral::DEFAULT);
endtask

task vmm_ral_block_or_sys::mirror(output vmm_rw::status_e status,
                                  input  vmm_ral::check_e check = vmm_ral::QUIET,
                                  input  vmm_ral::path_e  path  = vmm_ral::DEFAULT);
endtask

task vmm_ral_block_or_sys::readmemh(string filename);
endtask

task vmm_ral_block_or_sys::writememh(string filename);
endtask

function void vmm_ral_block_or_sys::prepend_callback(vmm_ral_callbacks cbs);
endfunction: prepend_callback


function void vmm_ral_block_or_sys::append_callback(vmm_ral_callbacks cbs);
endfunction: append_callback


function void vmm_ral_block_or_sys::unregister_callback(vmm_ral_callbacks cbs);
endfunction: unregister_callback


function int vmm_ral_block_or_sys::get_domain_index(string domain);
   // If the domain is "" and there is only one domain,
   // assume it is the one domain available to avoid
   // having to always have to specify domains
   if (domain == "" && this.domains.size() == 1) return 0;

   `foreach (this.domains,i) begin
      if (this.domains[i] == domain) return i;
   end
   `vmm_warning(this.log, $psprintf("Unknown domain name \"%s\" in %s.",
                                    domain, this.get_fullname()));
   return -1;
endfunction: get_domain_index


function int unsigned vmm_ral_block_or_sys::get_block_or_sys_ID();
   get_block_or_sys_ID =  this.block_or_sys_id;
endfunction

function int unsigned vmm_ral_block_or_sys::get_block_or_sys_size(string domain = "");
endfunction

function bit vmm_ral_block_or_sys::set_offset(bit [`VMM_RAL_ADDR_WIDTH-1:0] offset,
                                              string domain = "");
endfunction

function bit vmm_ral_block_or_sys::Xcheck_child_overlapX(int unsigned my_offset,
                                                         int unsigned my_size,
                                                         string domain = "",
                                                         vmm_ral_block blk,
                                                         vmm_ral_sys sys);
endfunction


function vmm_ral_block_or_sys vmm_ral_get_block_or_sys_by_ID(int unsigned id);
   vmm_ral_block_or_sys bos;
   if (bos.all_blocks_and_systems.exists(id))
      vmm_ral_get_block_or_sys_by_ID = bos.all_blocks_and_systems[id];
   else vmm_ral_get_block_or_sys_by_ID = null;
endfunction

