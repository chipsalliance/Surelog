// 
// -------------------------------------------------------------
//    Copyright 2004-2008 Synopsys, Inc.
//    Copyright 2008-2009 Mentor Graphics Corporation
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


class vmm_ral_reg_callbacks extends vmm_ral_callbacks;

   virtual task pre_write(vmm_ral_reg                       rg,
                          ref bit [`VMM_RAL_DATA_WIDTH-1:0] wdat,
                          ref vmm_ral::path_e               path,
                          ref string                        domain);
   endtask: pre_write

   virtual task post_write(vmm_ral_reg                   rg,
                           bit [`VMM_RAL_DATA_WIDTH-1:0] wdat,
                           vmm_ral::path_e               path,
                           string                        domain,
                           ref vmm_rw::status_e          status);
   endtask: post_write

   virtual task pre_read(vmm_ral_reg          rg,
                         ref vmm_ral::path_e  path,
                         ref string           domain);
   endtask: pre_read

   virtual task post_read(vmm_ral_reg                       rg,
                          ref bit [`VMM_RAL_DATA_WIDTH-1:0] rdat,
                          input vmm_ral::path_e             path,
                          input string                      domain,
                          ref vmm_rw::status_e              status);
   endtask: post_read
endclass: vmm_ral_reg_callbacks


virtual class vmm_ral_reg_frontdoor;
   static vmm_log log = new("vmm_ral_reg_frontdoor", "class");
   
   extern virtual task write(output vmm_rw::status_e              status,
                             input  bit [`VMM_RAL_DATA_WIDTH-1:0] data,
                             input  int                           data_id = -1,
                             input  int                           scenario_id = -1,
                             input  int                           stream_id = -1);
   extern virtual task read(output vmm_rw::status_e              status,
                            output bit [`VMM_RAL_DATA_WIDTH-1:0] data,
                            input  int                           data_id = -1,
                            input  int                           scenario_id = -1,
                            input  int                           stream_id = -1);
endclass: vmm_ral_reg_frontdoor



class vmm_ral_reg;
   static vmm_log log = new("RAL", "register");

   static vmm_ral_reg all_regs[`VMM_AA_INT]; // Keeps track of all registers in the RAL Model
   static local int unsigned reg_id_factory = 0;
   local int unsigned reg_id = 0;
   local bit locked;
   local vmm_ral_block parent;
   local string name;
   local int unsigned  n_bits;
   local int unsigned  n_used_bits;

   local logic [`VMM_RAL_ADDR_WIDTH-1:0] offset_in_block[];
   local string                          domains[];
   local vmm_ral::access_e               rights[];

   local vmm_ral_field fields[$];   // Fields in LSB to MSB order
   local string        constr[];
   local event         value_change;

   local vmm_ral_access        ral_access;
   local vmm_ral_reg_frontdoor frontdoor[];
   local vmm_ral_reg_backdoor  backdoor;

   local vmm_ral_reg_callbacks callbacks[$];

   local string attributes[string];

   local int has_cover;
   local int cover_on;

   local semaphore atomic;

   /*local*/ bit Xis_busyX;
   /*local*/ bit Xis_locked_by_fieldX;

   extern function new(vmm_ral_block                 parent,
                       string                        name,
                       int unsigned                  n_bits,
                       bit [`VMM_RAL_ADDR_WIDTH-1:0] offset,
                       string                        domain = "",
                       int                           cover_on = vmm_ral::NO_COVERAGE,
                       bit [1:0]                     rights = 2'b11,
                       bit                           unmapped = 0,
                       int                           has_cover = vmm_ral::NO_COVERAGE);

   /*local*/ extern function void Xlock_modelX();
   /*local*/ extern function void add_domain(bit [`VMM_RAL_ADDR_WIDTH-1:0] offset,
                                             string                        domain,
                                             bit [1:0]                     rights,
                                             bit                           unmapped = 0);
   
   local virtual function void domain_coverage(string domain,
                                               bit    rights,
                                               int    idx);
   endfunction
   
   /*local*/ extern function void register_field(vmm_ral_field field);
   /*local*/ extern function void Xregister_ral_accessX(vmm_ral_access access);
   /*local*/ extern function void Xadd_constraintsX(string name);
   /*local*/ extern task XatomicX(bit on);
   /*local*/ extern task XwriteX(output vmm_rw::status_e             status,
                                 input  bit[`VMM_RAL_DATA_WIDTH-1:0] value,
                                 input  vmm_ral::path_e              path,
                                 input  string                       domain,
                                 input  int                          data_id,
                                 input  int                          scenario_id,
                                 input  int                          stream_id);
   /*local*/ extern task XreadX(output vmm_rw::status_e             status,
                                output bit[`VMM_RAL_DATA_WIDTH-1:0] value,
                                input  vmm_ral::path_e              path,
                                input  string                       domain,
                                input  int                          data_id,
                                input  int                          scenario_id,
                                input  int                          stream_id);
   
   extern virtual function string get_name();
   extern virtual function string get_fullname();
   extern virtual function int get_n_domains();
   extern virtual function void get_domains(ref string domains[]);
   extern virtual function vmm_ral::access_e get_rights(string domain = "");
   extern virtual function vmm_ral_block get_block();
   extern virtual function bit [`VMM_RAL_ADDR_WIDTH-1:0] get_offset_in_block(string domain = ""); 
   extern virtual function bit [`VMM_RAL_ADDR_WIDTH-1:0] get_address_in_system(string domain = "");
   extern virtual function int unsigned get_n_bytes();
   extern virtual function void get_constraints(ref string names[]);

   extern virtual function void display(string prefix = "",
                                        string domain = "");
   extern virtual function string psdisplay(string prefix = "",
                                            string domain = "");

   extern virtual function void get_fields(ref vmm_ral_field fields[]);
   extern virtual function vmm_ral_field get_field_by_name(string name);

   extern virtual function void set_attribute(string name,
                                              string value);
   extern virtual function string get_attribute(string name,
                                                bit inherited = 1);
   extern virtual function void get_all_attributes(ref string names[],
                                                   input bit inherited = 1);

   extern virtual function bit can_cover(int models);
   extern virtual function int set_cover(int is_on);
   extern virtual function bit is_cover_on(int is_on);

   extern local virtual function void XforceX(bit [`VMM_RAL_DATA_WIDTH-1:0] value,
                                              vmm_ral::path_e               path,
                                              string                        domain);
   extern local virtual function void XwroteX(bit [`VMM_RAL_DATA_WIDTH-1:0] value,
                                              vmm_ral::path_e               path,
                                              string                        domain);
   extern virtual function void set(bit [`VMM_RAL_DATA_WIDTH-1:0] value);
   extern virtual function bit predict(bit [`VMM_RAL_DATA_WIDTH-1:0] value);
   extern virtual function bit[`VMM_RAL_DATA_WIDTH-1:0] get();
   extern virtual function void reset(vmm_ral::reset_e kind = vmm_ral::HARD);
   extern virtual function logic [`VMM_RAL_DATA_WIDTH-1:0]
                    get_reset(vmm_ral::reset_e kind = vmm_ral::HARD);
   extern virtual function bit needs_update(); 
 
   extern virtual task update(output vmm_rw::status_e status,
                              input  vmm_ral::path_e  path = vmm_ral::DEFAULT,
                              input  string           domain = "");
   extern virtual task write(output vmm_rw::status_e             status,
                             input  bit[`VMM_RAL_DATA_WIDTH-1:0] value,
                             input  vmm_ral::path_e              path = vmm_ral::DEFAULT,
                             input  string                       domain = "",
                             input  int                          data_id = -1,
                             input  int                          scenario_id = -1,
                             input  int                          stream_id = -1);
   extern virtual task read(output vmm_rw::status_e             status,
                            output bit[`VMM_RAL_DATA_WIDTH-1:0] value,
                            input  vmm_ral::path_e              path = vmm_ral::DEFAULT,
                            input  string                       domain = "",
                            input  int                          data_id = -1,
                            input  int                          scenario_id = -1,
                            input  int                          stream_id = -1);
   extern virtual task poke(output vmm_rw::status_e             status,
                            input  bit[`VMM_RAL_DATA_WIDTH-1:0] value,
                            input  int                          data_id = -1,
                            input  int                          scenario_id = -1,
                            input  int                          stream_id = -1);
   extern virtual task peek(output vmm_rw::status_e             status,
                            output bit[`VMM_RAL_DATA_WIDTH-1:0] value,
                            input  int                          data_id = -1,
                            input  int                          scenario_id = -1,
                            input  int                          stream_id = -1);
   extern virtual task mirror(output vmm_rw::status_e status,
                              input vmm_ral::check_e  check  = vmm_ral::QUIET,
                              input vmm_ral::path_e   path = vmm_ral::DEFAULT,
                              input string            domain = "");
  
   extern function void set_frontdoor(vmm_ral_reg_frontdoor ftdr,
                                      string                domain = "");
   extern function vmm_ral_reg_frontdoor get_frontdoor(string domain = "");
   extern function void set_backdoor(vmm_ral_reg_backdoor bkdr);
   extern function vmm_ral_reg_backdoor get_backdoor();

   extern function void prepend_callback(vmm_ral_reg_callbacks cb);
   extern function void append_callback(vmm_ral_reg_callbacks cb);
   extern function void unregister_callback(vmm_ral_reg_callbacks cb);

   extern local function int get_domain_index(string domain);
   extern virtual local function void sample(bit [`VMM_RAL_DATA_WIDTH-1:0] data,
                                             bit                           is_read,
                                             int                           domain);

   extern function int unsigned get_reg_ID();
endclass: vmm_ral_reg


function vmm_ral_reg::new(vmm_ral_block                 parent,
                          string                        name,
                          int unsigned                  n_bits,
                          bit [`VMM_RAL_ADDR_WIDTH-1:0] offset,
                          string                        domain = "",
                          int                           cover_on = vmm_ral::NO_COVERAGE,
                          bit [1:0]                     rights = 2'b11,
                          bit                           unmapped = 0,
                          int                           has_cover = vmm_ral::NO_COVERAGE);
   this.locked = 0;

   this.parent = parent;
   this.parent.register_reg(this);

   this.name = name;
   this.has_cover = has_cover;
   this.cover_on = vmm_ral::NO_COVERAGE;
   void'(this.set_cover(cover_on));

   if (n_bits == 0) begin
      `vmm_error(this.log, $psprintf("Register \"%s\" cannot have 0 bits", this.get_name()));
      n_bits = 1;
   end
   if (n_bits > `VMM_RAL_DATA_WIDTH) begin
      `vmm_error(this.log, $psprintf("Register \"%s\" cannot have more than %0d bits (%0d)", this.get_name(), `VMM_RAL_DATA_WIDTH, n_bits));
      n_bits = `VMM_RAL_DATA_WIDTH;
   end
   this.n_bits = n_bits;
   this.n_used_bits = 0;
   this.add_domain(offset, domain, rights, unmapped);

   this.atomic = new(1);

   this.Xis_busyX = 0;
   this.Xis_locked_by_fieldX = 1'b0;
   // Initialize Register ID
   this.reg_id = ++this.reg_id_factory;
   all_regs[this.reg_id] = this;
endfunction: new


function void vmm_ral_reg::Xlock_modelX();
   int idx;
   string fullname;

   if (this.locked) return;

   this.locked = 1;

endfunction: Xlock_modelX


function void vmm_ral_reg::add_domain(bit [`VMM_RAL_ADDR_WIDTH-1:0] offset,
                                      string                        domain,
                                      bit [1:0]                     rights,
                                      bit                           unmapped = 0);
   // Verify that this is a valid domain in the block
   string domains[];
   vmm_ral::access_e acc;

   if (this.locked) begin
      `vmm_error(this.log, "Cannot add domain to locked register model");
      return;
   end

   case (rights)
     2'b11: acc = vmm_ral::RW;
     2'b10: acc = vmm_ral::RO;
     2'b01: acc = vmm_ral::WO;
     default:
       `vmm_error(this.log,
                  $psprintf("Register \"%s\" has no access rights in domain \"%s\"",
                            this.get_name(), domain));
   endcase

   this.parent.get_domains(domains);
   foreach(domains[i]) begin
      if (domains[i] == domain) begin
         automatic int n = this.offset_in_block.size();
   
         this.offset_in_block = new [n + 1] (this.offset_in_block);
         this.offset_in_block[n] = (unmapped) ? 'x : offset;
    
         this.domains = new [n + 1] (this.domains);
         this.domains[n] = domain;

         this.rights = new [n + 1] (this.rights);
         this.rights[n] = acc;

         this.frontdoor = new [n + 1] (this.frontdoor);
         this.frontdoor[n] = null;

         this.domain_coverage(domain, rights, n);
         return;
      end
   end
   `vmm_error(this.log, $psprintf("Domain \"%s\" not found in parent block %s of register \"%s\"",
                                  domain, this.parent.get_name(), this.get_name()));
endfunction: add_domain


function void vmm_ral_reg::register_field(vmm_ral_field field);
   int offset;
   int idx;
   
   if (this.locked) begin
      `vmm_error(this.log, "Cannot add field to locked register model");
      return;
   end

   if (field == null) `vmm_fatal(this.log, "Attempting to register NULL field");

   // Store fields in LSB to MSB order
   offset = field.get_lsb_pos_in_register();

   idx = -1;
   `foreach (this.fields,i) begin
      if (offset < this.fields[i].get_lsb_pos_in_register()) begin
         int j = i;
         this.fields.insert(j, field);
         idx = i;
         break;
      end
   end
   if (idx < 0) begin
      this.fields.push_back(field);
      idx = this.fields.size()-1;
   end

   this.n_used_bits += field.get_n_bits();
   
   // Check if there are too many fields in the register
   if (this.n_used_bits > this.n_bits) begin
      `vmm_error(this.log, $psprintf("Fields use more bits (%0d) than available in register \"%s\" (%0d)",
                                     this.n_used_bits, this.get_name(), this.n_bits));
   end

   // Check if there are overlapping fields
   if (idx > 0) begin
      if (this.fields[idx-1].get_lsb_pos_in_register() +
          this.fields[idx-1].get_n_bits() > offset) begin
         `vmm_error(this.log, $psprintf("Field %s overlaps field %s in register \"%s\"",
                                        this.fields[idx-1].get_name(),
                                        field.get_name(), this.get_name()));
      end
   end
   if (idx < this.fields.size()-1) begin
      if (offset + field.get_n_bits() >
          this.fields[idx+1].get_lsb_pos_in_register()) begin
         `vmm_error(this.log, $psprintf("Field %s overlaps field %s in register \"%s\"",
                                        field.get_name(),
                                        this.fields[idx+1].get_name(),

                                      this.get_name()));
      end
   end
endfunction: register_field


function void vmm_ral_reg::Xregister_ral_accessX(vmm_ral_access access);
   // There can only be one RAL Access on a RAL model
   if (this.ral_access != null && this.ral_access != access) begin
      `vmm_fatal(this.log, $psprintf("Register \"%s\" is already used by another RAL access instance", this.get_name()));
   end
   this.ral_access = access;
endfunction: Xregister_ral_accessX


function void vmm_ral_reg::Xadd_constraintsX(string name);
   int n;

   if (this.locked) begin
      `vmm_error(this.log, "Cannot add constraints to locked register model");
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


task vmm_ral_reg::XatomicX(bit on);
   if (on) this.atomic.get(1);
   else begin
      // Maybe a key was put back in by a spurious call to reset()
      void'(this.atomic.try_get(1));
      this.atomic.put(1);
   end
endtask: XatomicX


function string vmm_ral_reg::get_name();
   get_name = this.name;
endfunction: get_name


function string vmm_ral_reg::get_fullname();
   vmm_ral_block blk;

   get_fullname = this.get_name();

   // Do not include top-level name in full name
   blk = this.get_block();
   if (blk == null) return get_fullname;
   if (blk.get_parent() == null) return get_fullname;

   get_fullname = {this.parent.get_fullname(), ".", get_fullname};
endfunction: get_fullname


function int vmm_ral_reg::get_n_domains();
   get_n_domains = this.domains.size();
endfunction: get_n_domains


function void vmm_ral_reg::get_domains(ref string domains[]);
   domains = new [this.domains.size()] (this.domains);
endfunction: get_domains


function vmm_ral::access_e vmm_ral_reg::get_rights(string domain = "");
   int i;

   // No right restrictions if not shared
   if (this.domains.size() == 1) begin
      return vmm_ral::RW;
   end

   i = this.get_domain_index(domain);
   if (i < 0) return vmm_ral::RW;

   get_rights = this.rights[i];
endfunction: get_rights


function vmm_ral_block vmm_ral_reg::get_block();
   get_block = this.parent;
endfunction: get_block


function bit [`VMM_RAL_ADDR_WIDTH-1:0] vmm_ral_reg::get_offset_in_block(string domain = "");
   `foreach (this.domains,i) begin
      if (this.domains[i] == domain) begin
         if (this.offset_in_block[i] === 'x) begin
            `vmm_warning(this.log, $psprintf("Register \"%s\" is unmapped in domain \"%s\".", this.get_name(), domain));
            return '0;
         end
         
         return this.offset_in_block[i];
      end
   end
   `vmm_warning(this.log, $psprintf("Unable to find offset within domain \"%s\" in register \"%s\".",
                                    domain, this.get_name()));
   get_offset_in_block = '1;
endfunction: get_offset_in_block


function bit [`VMM_RAL_ADDR_WIDTH-1:0] vmm_ral_reg::get_address_in_system(string domain = "");
   bit [`VMM_RAL_ADDR_WIDTH-1:0] addr[];
         
   int i = this.get_domain_index(domain);
   if (i < 0) return 0;

   if (this.ral_access == null) begin
      `vmm_fatal(this.parent.log,
                 "RAL model is not associated with an access transactor");
      return 0;
   end
         
   if (this.offset_in_block[i] === 'x) begin
      `vmm_error(this.log, $psprintf("Register \"%s\" is unmapped in domain \"%s\".", this.get_name(), this.domains[i]));
      return '1;
   end
         
   void'(this.ral_access.Xget_physical_addressesX(this.offset_in_block[i],
                                                  0, this.get_n_bytes(),
                                                  this.parent, this.domains[i],
                                                  addr));

   get_address_in_system = addr[addr.size()-1];

   // Make sure to return the lower address as Xget_physical_addressesX()
   // returns the address in little-endian sequence.
   if (addr[0] < get_address_in_system) get_address_in_system = addr[0];
endfunction: get_address_in_system


function int unsigned vmm_ral_reg::get_n_bytes();
   get_n_bytes = ((this.n_bits-1) / 8) + 1;
endfunction: get_n_bytes


function void vmm_ral_reg::display(string prefix = "",
                                   string domain = "");
   $write("%s\n", this.psdisplay(prefix, domain));
endfunction: display


function string vmm_ral_reg::psdisplay(string prefix = "",
                                       string domain = "");
   $sformat(psdisplay, "%sRegister %s -- %0d bytes @", prefix,
            this.get_fullname(), this.get_n_bytes());
   `foreach (this.domains,i) begin
      if (this.domains[i] == domain) begin
         if (this.offset_in_block[i] === 'x) begin
            psdisplay = {psdisplay, "none"};
         end
         else begin
            $sformat(psdisplay, "%s'h%h", psdisplay,
                     this.get_address_in_system(domain));
         end
         break;
      end
   end
   if (this.attributes.num() > 0) begin
      string name;
      this.attributes.first(name);
      psdisplay = {psdisplay, "\n", prefix, "Attributes:"};
      do begin
         string attr = this.attributes[name];
         $sformat(psdisplay, " %s=\"%s\"", name, attr);
      end while (this.attributes.next(name));
   end
   `foreach(this.fields,i) begin
      $sformat(psdisplay, "%s\n%s", psdisplay,
               this.fields[i].psdisplay({prefix, "   "}));
   end
endfunction: psdisplay


function void vmm_ral_reg::get_fields(ref vmm_ral_field fields[]);
   fields = new [this.fields.size()];
   `foreach(this.fields,i) begin
      fields[i] = this.fields[i];
   end
endfunction: get_fields


function vmm_ral_field vmm_ral_reg::get_field_by_name(string name);
   `foreach (this.fields,i) begin
      if (this.fields[i].get_name() == name) begin
         return this.fields[i];
      end
   end
   `vmm_warning(this.log, $psprintf("Unable to locate field \"%s\" in register \"%s\".",
                                    name, this.get_name()));
   get_field_by_name = null;
endfunction: get_field_by_name


function void vmm_ral_reg::get_constraints(ref string names[]);
   names = new [this.constr.size()] (this.constr);
endfunction: get_constraints


function void vmm_ral_reg::set_attribute(string name,
                                         string value);
   if (name == "") begin
      `vmm_error(this.log, $psprintf("Cannot set anonymous attribute \"\" in register \"%s\". Please specify an attribute name.",
                                       name, this.get_fullname()));
      return;
   end

   if (this.attributes.exists(name)) begin
      if (value != "") begin
         `vmm_warning(this.log, $psprintf("Redefining attributed \"%s\" in register \"%s\" to \"%s\".",
                                          name, this.get_fullname(), value));
         this.attributes[name] = value;
      end
      else begin
         this.attributes.delete(name);
      end
      return;
   end

   if (value == "") begin
      `vmm_warning(this.log, $psprintf("Attempting to delete non-existent attribute \"%s\" in register \"%s\".",
                                       name, this.get_fullname()));
      return;
   end

   this.attributes[name] = value;
endfunction: set_attribute


function string vmm_ral_reg::get_attribute(string name,
                                           bit inherited = 1);
   if (this.attributes.exists(name)) begin
      return this.attributes[name];
   end

   if (inherited) return this.parent.get_attribute(name);

   return "";
endfunction: get_attribute


function void vmm_ral_reg::get_all_attributes(ref string names[],
                                              input bit inherited = 1);
   string tmp[];
   string name;
   bit    ok;
   int    i;

   if (inherited) this.parent.get_all_attributes(tmp);

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


function bit vmm_ral_reg::can_cover(int models);
   return ((this.has_cover & models) == models);
endfunction: can_cover


function int vmm_ral_reg::set_cover(int is_on);
   if (is_on == vmm_ral::NO_COVERAGE) begin
      this.cover_on = is_on;
      return this.cover_on;
   end

   if ((this.has_cover & is_on) == 0) begin
      `vmm_warning(this.log, $psprintf("Register \"%s\" - Cannot turn ON any coverage becasue the corresponding coverage model was not generated.", this.get_fullname()));
      return this.cover_on;
   end

   if (is_on & vmm_ral::REG_BITS) begin
      if (this.has_cover & vmm_ral::REG_BITS) begin
          this.cover_on |= vmm_ral::REG_BITS;
      end else begin
          `vmm_warning(this.log, $psprintf("Register \"%s\" - Cannot turn ON Register Bit coverage becasue the corresponding coverage model was not generated.", this.get_fullname()));
      end
   end

   if (is_on & vmm_ral::FIELD_VALS) begin
      if (this.has_cover & vmm_ral::FIELD_VALS) begin
          this.cover_on |= vmm_ral::FIELD_VALS;
      end else begin
          `vmm_warning(this.log, $psprintf("Register \"%s\" - Cannot turn ON Field Value coverage becasue the corresponding coverage model was not generated.", this.get_fullname()));
      end
   end

   if (is_on & vmm_ral::ADDR_MAP) begin
      if (this.has_cover & vmm_ral::ADDR_MAP) begin
          this.cover_on |= vmm_ral::ADDR_MAP;
      end else begin
          `vmm_warning(this.log, $psprintf("Register \"%s\" - Cannot turn ON Address Map coverage becasue the corresponding coverage model was not generated.", this.get_fullname()));
      end
   end

   set_cover = this.cover_on;
endfunction: set_cover


function bit vmm_ral_reg::is_cover_on(int is_on);
   if (this.can_cover(is_on) == 0) return 0;
   return ((this.cover_on & is_on) == is_on);
endfunction: is_cover_on


function void vmm_ral_reg::XforceX(bit [`VMM_RAL_DATA_WIDTH-1:0] value,
                                   vmm_ral::path_e               path,
                                   string                        domain);
   // Fields are stored in LSB or MSB order
   `foreach (this.fields,i) begin
      this.fields[i].XforceX(value >> this.fields[i].get_lsb_pos_in_register(),
                             path, domain);
   end
endfunction: XforceX


function void vmm_ral_reg::XwroteX(bit [`VMM_RAL_DATA_WIDTH-1:0] value,
                                   vmm_ral::path_e               path,
                                   string                        domain);
   int j, w;

   // Fields are stored in LSB or MSB order
   `foreach (this.fields,i) begin
      j = this.fields[i].get_lsb_pos_in_register();
      w = this.fields[i].get_n_bits();
      this.fields[i].XwroteX((value >> j) & ((1 << w) - 1), path, domain);
   end
endfunction: XwroteX


function void vmm_ral_reg::set(bit [`VMM_RAL_DATA_WIDTH-1:0] value);
   // Split the value into the individual fields
   int j, w;

   // Fields are stored in LSB or MSB order
   `foreach (this.fields,i) begin
      j = this.fields[i].get_lsb_pos_in_register();
      w = this.fields[i].get_n_bits();
      this.fields[i].set((value >> j) & ((1 << w) - 1));
   end
endfunction: set


function bit vmm_ral_reg::predict(bit [`VMM_RAL_DATA_WIDTH-1:0] value);
   if (this.Xis_busyX) begin
      `vmm_warning(this.log, $psprintf("Trying to predict value of register \"%s\" while it is being accessed",
                                       this.get_fullname()));
      return 0;
   end
   
   predict = 1;
   
   // Fields are stored in LSB or MSB order
   `foreach (this.fields,i) begin
      predict &= this.fields[i].predict(value >> this.fields[i].get_lsb_pos_in_register());
   end
endfunction: predict


function bit[`VMM_RAL_DATA_WIDTH-1:0] vmm_ral_reg::get();
   // Concatenate the value of the individual fields
   // to form the register value
   int j, w;

   get = 0;
   
   // Fields are stored in LSB or MSB order
   `foreach (this.fields,i) begin
      j = this.fields[i].get_lsb_pos_in_register();
      get |= this.fields[i].get() << j;
   end
endfunction: get


function logic [`VMM_RAL_DATA_WIDTH-1:0]
   vmm_ral_reg::get_reset(vmm_ral::reset_e kind = vmm_ral::HARD);
   // Concatenate the value of the individual fields
   // to form the register value
   int j, w;

   get_reset = 0;
   
   // Fields are stored in LSB or MSB order
   `foreach (this.fields,i) begin
      j = this.fields[i].get_lsb_pos_in_register();
      get_reset |= this.fields[i].get_reset(kind) << j;
   end
endfunction: get_reset


function void vmm_ral_reg::reset(vmm_ral::reset_e kind = vmm_ral::HARD);
   `foreach (this.fields,i) begin
      this.fields[i].reset(kind);
   end
   // Put back a key in the semaphore if it is checked out
   // in case a thread was killed during an operation
   void'(this.atomic.try_get(1));
   this.atomic.put(1);
endfunction: reset


function bit vmm_ral_reg::needs_update();
   needs_update = 0;
   `foreach (this.fields,i) begin
      if (this.fields[i].needs_update()) begin
         return 1;
      end
   end
endfunction: needs_update


task vmm_ral_reg::update(output vmm_rw::status_e status,
                         input  vmm_ral::path_e  path = vmm_ral::DEFAULT,
                         input  string           domain = "");
   bit [`VMM_RAL_DATA_WIDTH-1:0] upd;
   int j;

   if (this.parent.Xis_powered_downX) begin
      `vmm_error(this.log, $psprintf("Register %s cannot be accessed when its parent block is powered down", this.get_fullname()));
      return;
   end

   status = vmm_rw::IS_OK;
   if (!this.needs_update()) return;

   this.XatomicX(1);

   // Concatenate the write-to-update values from each field
   // Fields are stored in LSB or MSB order
   upd = 0;
   `foreach (this.fields,i) begin
      j = this.fields[i].get_lsb_pos_in_register();
      upd |= this.fields[i].XupdX() << j;
   end

   this.XwriteX(status, upd, path, domain, -1, -1, -1);

   this.XatomicX(0);
endtask: update


task vmm_ral_reg::write(output vmm_rw::status_e             status,
                        input  bit[`VMM_RAL_DATA_WIDTH-1:0] value,
                        input  vmm_ral::path_e              path = vmm_ral::DEFAULT,
                        input  string                       domain = "",
                        input  int                          data_id = -1,
                        input  int                          scenario_id = -1,
                        input  int                          stream_id = -1);
   if (this.parent.Xis_powered_downX) begin
      `vmm_error(this.log, $psprintf("Register %s cannot be accessed when its parent block is powered down", this.get_fullname()));
      return;
   end

   this.XatomicX(1);
   this.XwriteX(status, value, path, domain, data_id, scenario_id, stream_id);
   this.XatomicX(0);
endtask: write


task vmm_ral_reg::XwriteX(output vmm_rw::status_e             status,
                          input  bit[`VMM_RAL_DATA_WIDTH-1:0] value,
                          input  vmm_ral::path_e              path,
                          input  string                       domain,
                          input  int                          data_id,
                          input  int                          scenario_id,
                          input  int                          stream_id);
   status = vmm_rw::ERROR;
   
   if (this.ral_access == null) begin
      `vmm_error(this.log, $psprintf("Register \"%s\" not associated with RAL access object", this.get_name()));
      return;
   end
   
   if (path == vmm_ral::DEFAULT) path = this.parent.get_default_access();

   begin
      bit [`VMM_RAL_DATA_WIDTH-1:0] tmp;
      bit [`VMM_RAL_DATA_WIDTH-1:0] msk;
      int lsb;

      foreach (fields[i]) begin
         vmm_ral_field f = fields[i];

         lsb = f.get_lsb_pos_in_register();

         msk = ((1<<f.get_n_bits())-1) << lsb;
         tmp = (value & msk) >> lsb;

         `foreach (f.XcbsX,j) begin
            vmm_ral_field_callbacks cb;
            if (!$cast(cb, f.XcbsX[j])) continue;
            cb.pre_write(f, tmp, path, domain);
         end

         value = (value & ~msk) | (tmp << lsb);
      end
   end
   `vmm_callback(vmm_ral_reg_callbacks,
              pre_write(this, value, path, domain));

   if (path == vmm_ral::DEFAULT) path = this.parent.get_default_access();

   if (path == vmm_ral::BACKDOOR &&
       this.backdoor == null) begin
      `vmm_warning(this.log, $psprintf("No backdoor access available for register \"%s\". Using frontdoor instead.", this.get_name()));
      path = vmm_ral::BFM;
   end

   case (path)
      
      vmm_ral::BFM: begin
         int di = this.get_domain_index(domain);
         if (di < 0) return;
         
         this.Xis_busyX = 1;

         if (this.frontdoor[di] != null) begin
            this.frontdoor[di].write(status, value,
                                     data_id, scenario_id, stream_id);
         end
         else begin
            bit [`VMM_RAL_ADDR_WIDTH-1:0] addr[];
            int w, j;
            int n_bits;

            if (this.offset_in_block[di] === 'x) begin
               `vmm_error(this.log, $psprintf("Register \"%s\" unmapped in domain \"%s\" does not have a user-defined frontdoor",
                                              this.get_name(),
                                              this.domains[di]));
               return;
            end

            w = this.ral_access.Xget_physical_addressesX(this.offset_in_block[di],
                                                         0, this.get_n_bytes(),
                                                         this.parent,
                                                         this.domains[di],
                                                         addr);
            j = 0;
            n_bits = this.get_n_bytes() * 8;
            foreach (addr[i]) begin
               bit [`VMM_RAL_DATA_WIDTH-1:0] data;
               data = value >> (j*8);
               this.ral_access.write(status, addr[i], data,
                                     (n_bits > w*8) ? w*8 : n_bits,
                                     this.parent.get_external_domain(this.domains[di]),
                                     data_id, scenario_id, stream_id);
               if (status != vmm_rw::IS_OK) return;
               j += w;
               n_bits -= w * 8;
            end
         end

         if (this.cover_on) begin
            this.sample(value, 0, di);
            this.parent.XsampleX(this.offset_in_block[di], di);
         end

         this.Xis_busyX = 0;

         this.XwroteX(value, path, domain);
      end
      
      vmm_ral::BACKDOOR: begin
         bit [`VMM_RAL_DATA_WIDTH-1:0] reg_val;
         bit [`VMM_RAL_DATA_WIDTH-1:0] final_val;

         // Mimick the final value after a physical read
         this.backdoor.read(status, reg_val,
                            data_id, scenario_id, stream_id);
         if (status != vmm_rw::IS_OK) return;

         begin
            int j, w;

            // Fields are stored in LSB or MSB order
            final_val = '0;
            `foreach (this.fields,i) begin
               bit [`VMM_RAL_DATA_WIDTH-1:0] field_val;
               j = this.fields[i].get_lsb_pos_in_register();
               w = this.fields[i].get_n_bits();
               field_val = this.fields[i].XpredictX((reg_val >> j) & ((1 << w) - 1),
                                                    (value >> j) & ((1 << w) - 1),
                                                    domain);
               final_val |= field_val << j;
            end
         end
         this.backdoor.write(status, final_val, data_id, scenario_id, stream_id);
         this.XwroteX(final_val, path, "-");
      end
   endcase

   begin
      bit [`VMM_RAL_DATA_WIDTH-1:0] tmp;
      bit [`VMM_RAL_DATA_WIDTH-1:0] msk;
      int lsb;

      value = this.get();

      foreach (fields[i]) begin
         vmm_ral_field f = fields[i];

         lsb = f.get_lsb_pos_in_register();

         msk = ((1<<f.get_n_bits())-1) << lsb;
         tmp = (value & msk) >> lsb;

         `foreach (f.XcbsX,j) begin
            vmm_ral_field_callbacks cb;
            if (!$cast(cb, f.XcbsX[j])) continue;
            cb.post_write(f, tmp, path, domain, status);
         end
      end
   end

   `vmm_trace(this.log, $psprintf("Wrote register \"%s\" via %s with: 'h%h",
                                  this.get_fullname(),
                                  (path == vmm_ral::BFM) ? "frontdoor" : "backdoor",
                                  value));

   `vmm_callback(vmm_ral_reg_callbacks,
                 post_write(this, value, path, domain, status));
endtask: XwriteX


task vmm_ral_reg::read(output vmm_rw::status_e             status,
                       output bit[`VMM_RAL_DATA_WIDTH-1:0] value,
                       input  vmm_ral::path_e              path = vmm_ral::DEFAULT,
                       input  string                       domain = "",
                       input  int                          data_id = -1,
                       input  int                          scenario_id = -1,
                       input  int                          stream_id = -1);
   if (this.parent.Xis_powered_downX) begin
      `vmm_error(this.log, $psprintf("Register %s cannot be accessed when its parent block is powered down", this.get_fullname()));
      return;
   end

   this.XatomicX(1);
   this.XreadX(status, value, path, domain, data_id, scenario_id, stream_id);
   this.XatomicX(0);
endtask: read


task vmm_ral_reg::XreadX(output vmm_rw::status_e             status,
                         output bit[`VMM_RAL_DATA_WIDTH-1:0] value,
                         input  vmm_ral::path_e              path,
                         input  string                       domain,
                         input  int                          data_id,
                         input  int                          scenario_id,
                         input  int                          stream_id);
   status = vmm_rw::ERROR;
   
   if (this.ral_access == null) begin
      `vmm_error(this.log, $psprintf("Register \"%s\" not associated with RAL access object", this.get_name()));
      return;
   end
   
   if (path == vmm_ral::DEFAULT) path = this.parent.get_default_access();

   foreach (fields[i]) begin
      vmm_ral_field f = fields[i];

      `foreach (f.XcbsX,j) begin
         vmm_ral_field_callbacks cb;
         if (!$cast(cb, f.XcbsX[j])) continue;
         cb.pre_read(f, path, domain);
      end
   end
   `vmm_callback(vmm_ral_reg_callbacks,
                 pre_read(this, path, domain));

   if (path == vmm_ral::DEFAULT) path = this.parent.get_default_access();

   if (path == vmm_ral::BACKDOOR &&
       this.backdoor == null) begin
      `vmm_warning(this.log, $psprintf("No backdoor access available for register \"%s\". Using frontdoor instead.", this.get_name()));
      path = vmm_ral::BFM;
   end

   case (path)
      
      vmm_ral::BFM: begin
         int di = this.get_domain_index(domain);
         if (di < 0) return;
         
         this.Xis_busyX = 1;

         if (this.frontdoor[di] != null) begin
            this.frontdoor[di].read(status, value,
                                   data_id, scenario_id, stream_id);
         end
         else begin
            bit [`VMM_RAL_ADDR_WIDTH-1:0] addr[];
            int w, j;
            int n_bits;
         
            if (this.offset_in_block[di] === 'x) begin
               `vmm_error(this.log, $psprintf("Register \"%s\" unmapped in domain \"%s\" does not have a user-defined frontdoor",
                                              this.get_name(),
                                              this.domains[di]));
               return;
            end
         
            w = this.ral_access.Xget_physical_addressesX(this.offset_in_block[di],
                                                         0, this.get_n_bytes(),
                                                         this.parent,
                                                         this.domains[di],
                                                         addr);
            j = 0;
            n_bits = this.get_n_bytes() * 8;
            value = 0;
            foreach (addr[i]) begin
               bit [`VMM_RAL_DATA_WIDTH-1:0] data;
               this.ral_access.read(status, addr[i], data,
                                    (n_bits > w*8) ? w*8 : n_bits,
                                    this.parent.get_external_domain(this.domains[di]),
                                    data_id, scenario_id, stream_id);
               if (status != vmm_rw::IS_OK) return;
               value |= (data & ((1 << (w*8)) - 1)) << (j*8);
               j += w;
               n_bits -= w * 8;
            end
         end

         if (this.cover_on) begin
            this.sample(value, 1, di);
            this.parent.XsampleX(this.offset_in_block[di], di);
         end

         this.Xis_busyX = 0;

         this.XforceX(value, path, domain);
      end
      
      vmm_ral::BACKDOOR: begin
         bit [`VMM_RAL_DATA_WIDTH-1:0] final_val;

         this.backdoor.read(status, value, data_id, scenario_id, stream_id);
         final_val = value;

         // Need to clear RC fields and mask WO fields
         if (status == vmm_rw::IS_OK) begin
            bit [`VMM_RAL_DATA_WIDTH-1:0] wo_mask = 0;

            `foreach (this.fields,i) begin
               vmm_ral::access_e acc = this.fields[i].get_access("BaCkDoOr");
               if (acc == vmm_ral::RC) begin
                  final_val &= ~(((1<<this.fields[i].get_n_bits())-1) << this.fields[i].get_lsb_pos_in_register());
               end
               else if (acc == vmm_ral::WO) begin
                  wo_mask |= ((1<<this.fields[i].get_n_bits())-1) << this.fields[i].get_lsb_pos_in_register();
               end
            end

            if (final_val != value) begin
               this.backdoor.write(status, final_val,
                                   data_id, scenario_id, stream_id);
            end

            value &= ~wo_mask;
            this.XforceX(final_val, path, "-");
         end
      end
   endcase


   begin
      bit [`VMM_RAL_DATA_WIDTH-1:0] tmp;
      bit [`VMM_RAL_DATA_WIDTH-1:0] msk;
      int lsb;

      foreach (fields[i]) begin
         vmm_ral_field f = fields[i];

         lsb = f.get_lsb_pos_in_register();

         msk = ((1<<f.get_n_bits())-1) << lsb;
         tmp = (value & msk) >> lsb;

         `foreach (f.XcbsX,j) begin
            vmm_ral_field_callbacks cb;
            if (!$cast(cb, f.XcbsX[j])) continue;
            cb.post_read(f, tmp, path, domain, status);
         end

         value = (value & ~msk) | (tmp << lsb);
      end
   end

   `vmm_trace(this.log, $psprintf("Read register \"%s\" via %s: 'h%h",
                                  this.get_fullname(),
                                  (path == vmm_ral::BFM) ? "frontdoor" : "backdoor",
                                  value));

   `vmm_callback(vmm_ral_reg_callbacks,
                 post_read(this, value, path, domain, status));
endtask: XreadX


task vmm_ral_reg::poke(output vmm_rw::status_e             status,
                       input  bit[`VMM_RAL_DATA_WIDTH-1:0] value,
                       input  int                          data_id = -1,
                       input  int                          scenario_id = -1,
                       input  int                          stream_id = -1);
   if (this.parent.Xis_powered_downX) begin
      `vmm_error(this.log, $psprintf("Register %s cannot be accessed when its parent block is powered down", this.get_fullname()));
      return;
   end

   if(!this.Xis_locked_by_fieldX)
     this.XatomicX(1);

   if (this.backdoor == null) begin
      `vmm_error(this.log, $psprintf("No backdoor access available to poke register \"%s\"", this.get_name()));
      status = vmm_rw::ERROR;
      if(!this.Xis_locked_by_fieldX)
        this.XatomicX(0);
      return;
   end

   this.backdoor.write(status, value, data_id, scenario_id, stream_id);

   `vmm_trace(this.log, $psprintf("Poked register \"%s\" with: 'h%h",
                                  this.get_fullname(), value));

   this.XforceX(value, vmm_ral::BACKDOOR, "-");
   if(!this.Xis_locked_by_fieldX)
     this.XatomicX(0);
endtask: poke


task vmm_ral_reg::peek(output vmm_rw::status_e             status,
                       output bit[`VMM_RAL_DATA_WIDTH-1:0] value,
                       input  int                          data_id = -1,
                       input  int                          scenario_id = -1,
                       input  int                          stream_id = -1);
   if (this.parent.Xis_powered_downX) begin
      `vmm_error(this.log, $psprintf("Register %s cannot be accessed when its parent block is powered down", this.get_fullname()));
      return;
   end

   if(!this.Xis_locked_by_fieldX)
     this.XatomicX(1);
   if (this.backdoor == null) begin
      `vmm_error(this.log, $psprintf("No backdoor access available peek register \"%s\"", this.get_name()));
      status = vmm_rw::ERROR;
      if(!this.Xis_locked_by_fieldX)
        this.XatomicX(0);
      return;
   end
   this.backdoor.read(status, value, data_id, scenario_id, stream_id);

   `vmm_trace(this.log, $psprintf("Peeked register \"%s\": 'h%h",
                                  this.get_fullname(), value));

   this.XforceX(value, vmm_ral::BACKDOOR, "-");

   if(!this.Xis_locked_by_fieldX)
     this.XatomicX(0);
endtask: peek


task vmm_ral_reg::mirror(output vmm_rw::status_e  status,
                         input  vmm_ral::check_e  check = vmm_ral::QUIET,
                         input  vmm_ral::path_e   path = vmm_ral::DEFAULT,
                         input  string            domain = "");
   bit [`VMM_RAL_DATA_WIDTH-1:0] v;
   bit [`VMM_RAL_DATA_WIDTH-1:0] exp;

   if (this.parent.Xis_powered_downX) begin
      `vmm_error(this.log, $psprintf("Register %s cannot be accessed when its parent block is powered down", this.get_fullname()));
      return;
   end

   if (path == vmm_ral::DEFAULT) path = this.parent.get_default_access();

   this.XatomicX(1);

   if (path == vmm_ral::BACKDOOR && this.backdoor != null) begin
      domain = "BaCkDoOr";
   end

   // Remember what we think the value is before it gets updated
   if (check == vmm_ral::VERB) begin
      exp = this.get();
      // Any WO field will readback as 0's
      `foreach(this.fields,i) begin
         if (this.fields[i].get_access(domain) == vmm_ral::WO) begin
            exp &= ~(((1 << this.fields[i].get_n_bits())-1)
                     << this.fields[i].get_lsb_pos_in_register());
         end
      end
   end

   this.XreadX(status, v, path, domain, -1, -1, -1);

   if (status != vmm_rw::IS_OK) begin
      this.XatomicX(0);
      return;
   end

   if (check == vmm_ral::VERB) begin
      // Check that our idea of the register value matches
      // what we just read from the DUT, minus the don't care fields
      bit [`VMM_RAL_DATA_WIDTH-1:0] dc = 0;

      `foreach(this.fields,i) begin
         vmm_ral::access_e acc = this.fields[i].get_access(domain);
         if (acc == vmm_ral::DC) begin
            dc |= ((1 << this.fields[i].get_n_bits())-1)
                  << this.fields[i].get_lsb_pos_in_register();
         end
         else if (acc == vmm_ral::WO) begin
            // WO fields will always read-back as 0
            exp &= ~(((1 << this.fields[i].get_n_bits())-1)
                     << this.fields[i].get_lsb_pos_in_register());
         end
      end

      if ((v|dc) !== (exp|dc)) begin
         `vmm_error(this.log, $psprintf("Register \"%s\" value read from DUT (0x%h) does not match mirrored value (0x%h)",
                                        this.get_name(), v, (exp ^ ('x & dc))));
      end
   end

   this.XatomicX(0);
endtask: mirror


function void vmm_ral_reg::set_frontdoor(vmm_ral_reg_frontdoor ftdr,
                                         string                domain = "");
   `foreach(this.domains,i) begin
      if (this.domains[i] == domain) begin
         this.frontdoor[i] = ftdr;
         return;
      end
   end
   `vmm_error(this.log, $psprintf("Domain \"%s\" not found in register %s", domain, this.get_fullname()));
endfunction: set_frontdoor


function vmm_ral_reg_frontdoor vmm_ral_reg::get_frontdoor(string domain = "");
   `foreach(this.domains,i) begin
      if (this.domains[i] == domain) begin
         return this.frontdoor[i];
      end
   end
   `vmm_error(this.log, $psprintf("Domain \"%s\" not found in register %s", domain, this.get_fullname()));
endfunction: get_frontdoor


function void vmm_ral_reg::set_backdoor(vmm_ral_reg_backdoor bkdr);
   this.backdoor = bkdr;
endfunction: set_backdoor


function vmm_ral_reg_backdoor vmm_ral_reg::get_backdoor();
   get_backdoor = this.backdoor;
endfunction: get_backdoor


function void vmm_ral_reg::prepend_callback(vmm_ral_reg_callbacks cb);
   `foreach (this.callbacks,i) begin
      if (this.callbacks[i] == cb) begin
         `vmm_warning(this.log, $psprintf("Callback has already been registered with register \"%s\"", this.get_name()));
         return;
      end
   end
   
   // Prepend new callback
   this.callbacks.push_front(cb);
endfunction: prepend_callback


function void vmm_ral_reg::append_callback(vmm_ral_reg_callbacks cb);
   `foreach (this.callbacks,i) begin
      if (this.callbacks[i] == cb) begin
         `vmm_warning(this.log, $psprintf("Callback has already been registered with register \"%s\"", this.get_name()));
         return;
      end
   end
   
   // Append new callback
   this.callbacks.push_back(cb);
endfunction: append_callback


function void vmm_ral_reg::unregister_callback(vmm_ral_reg_callbacks cb);
   `foreach (this.callbacks,i) begin
      if (this.callbacks[i] == cb) begin
         int j = i;
         // Unregister it
         this.callbacks.delete(j);
         return;
      end
   end

   `vmm_warning(this.log, $psprintf("Callback was not registered with register \"%s\"", this.get_name()));
endfunction: unregister_callback


function int vmm_ral_reg::get_domain_index(string domain);
   // If the domain is "" and there is only one domain,
   // assume it is the one domain available to avoid
   // having to always have to specify domains
   if (domain == "" && this.domains.size() == 1) return 0;

   `foreach (this.domains,i) begin
      if (this.domains[i] == domain) return i;
   end
   `vmm_warning(this.log, $psprintf("Unknown domain name \"%s\" in register \"%s\".", domain, this.get_name()));
   return -1;
endfunction: get_domain_index


task vmm_ral_reg_frontdoor::write(output vmm_rw::status_e              status,
                                  input  bit [`VMM_RAL_DATA_WIDTH-1:0] data,
                                  input  int                           data_id = -1,
                                  input  int                           scenario_id = -1,
                                  input  int                           stream_id = -1);
   `vmm_fatal(this.log, "vmm_ral_reg_frontdoor::write() method has not been overloaded");
endtask: write


task vmm_ral_reg_frontdoor::read(output vmm_rw::status_e              status,
                                 output bit [`VMM_RAL_DATA_WIDTH-1:0] data,
                                 input  int                           data_id = -1,
                                 input  int                           scenario_id = -1,
                                 input  int                           stream_id = -1);
   `vmm_fatal(this.log, "vmm_ral_reg_frontdoor::read() method has not been overloaded");
endtask: read


function void vmm_ral_reg::sample(bit [`VMM_RAL_DATA_WIDTH-1:0] data,
                                  bit                           is_read,
                                  int                           domain);
   // Nothing to do in this base class
endfunction


function int unsigned vmm_ral_reg::get_reg_ID();
   get_reg_ID =  this.reg_id;
endfunction

function vmm_ral_reg vmm_ral_get_reg_by_ID(int unsigned id);
   vmm_ral_reg rg;
   if (rg.all_regs.exists(id)) 
      vmm_ral_get_reg_by_ID = rg.all_regs[id];
   else vmm_ral_get_reg_by_ID = null;
endfunction

