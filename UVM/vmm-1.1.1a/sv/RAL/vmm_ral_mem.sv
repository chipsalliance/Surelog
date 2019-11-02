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


function vmm_ral_mem::new(vmm_ral_block                 parent,
                          string                        name,
                          vmm_ral::access_e             access,
                          longint unsigned              size,
                          int unsigned                  n_bits,
                          bit [`VMM_RAL_ADDR_WIDTH-1:0] base_addr,
                          string                        domain = "",
                          int                           cover_on = vmm_ral::NO_COVERAGE,
                          bit [1:0]                     rights = 2'b11,
                          bit                           unmapped = 0,
                          int                           has_cover = vmm_ral::NO_COVERAGE);

   this.name = name;
   this.locked = 0;

   if (n_bits == 0) begin
      `vmm_error(this.log, $psprintf("Memory \"%s\" cannot have 0 bits", this.get_fullname()));
      n_bits = 1;
   end
   if (n_bits > `VMM_RAL_DATA_WIDTH) begin
      `vmm_error(this.log, $psprintf("Memory \"%s\" cannot have more than %0d bits (%0d)", this.get_fullname(), `VMM_RAL_DATA_WIDTH, n_bits));
      n_bits = `VMM_RAL_DATA_WIDTH;
   end
   if (access != vmm_ral::RW && access != vmm_ral::RO) begin
      `vmm_error(this.log, $psprintf("Memory %s can only be RW or RO",
                                     this.get_fullname()));
      access = vmm_ral::RW;
   end

   this.parent   = parent;
   this.size     = size;
   this.access   = access;
   this.n_bits   = n_bits;
   this.backdoor  = null;

   this.parent.register_mem(this);
   this.add_domain(base_addr, domain, rights, unmapped);

   this.is_powered_down = 0;

   this.has_cover = has_cover;
   this.cover_on = vmm_ral::NO_COVERAGE;
   void'(this.set_cover(cover_on));

   begin
      vmm_mam_cfg cfg = new;

      cfg.n_bytes      = ((n_bits-1) / 8) + 1;
      cfg.start_offset = 0;
      cfg.end_offset   = size-1;

      cfg.mode     = vmm_mam::GREEDY;
      cfg.locality = vmm_mam::BROAD;

      this.mam = new(this.get_fullname(), cfg, this);
   end

   // Initialize Memory ID
   this.mem_id = ++this.mem_id_factory;
   all_mems[this.mem_id] = this;
endfunction: new


function void vmm_ral_mem::Xlock_modelX();
   this.locked = 1;
endfunction: Xlock_modelX


function void vmm_ral_mem::add_domain(bit [`VMM_RAL_ADDR_WIDTH-1:0] base_addr,
                                      string                        domain,
                                      bit [1:0]                     rights,
                                      bit                           unmapped = 0);
   vmm_ral::access_e acc;

   // Verify that this is a valid domain in the block
   string domains[];

   if (this.locked) begin
      `vmm_error(this.log, $psprintf("Cannot add domain to locked memory %s", this.get_fullname()));
      return;
   end

   case (rights)
     2'b11: acc = vmm_ral::RW;
     2'b10: acc = vmm_ral::RO;
     2'b01: acc = vmm_ral::WO;
     default:
       `vmm_error(this.log,
                  $psprintf("Memory %s has no access rights in domain \"%s\"",
                            this.get_fullname(), domain));
   endcase

   this.parent.get_domains(domains);
   foreach(domains[i]) begin
      if (domains[i] == domain) begin
         automatic int n = this.offset_in_block.size();
   
         this.offset_in_block = new [n + 1] (this.offset_in_block);
         this.offset_in_block[n] = (unmapped) ? 'X : base_addr;
    
         this.domains = new [n + 1] (this.domains);
         this.domains[n] = domain;

         this.rights = new [n + 1] (this.rights);
         this.rights[n] = acc;

         this.frontdoor = new [n + 1] (this.frontdoor);
         this.frontdoor[n] = null;
         return;
      end
   end
   `vmm_error(this.log, $psprintf("Domain \"%s\" not found in parent block %s of memory %s",
                                  domain, this.parent.get_name(), this.get_fullname()));
endfunction: add_domain


function void vmm_ral_mem::Xregister_ral_accessX(vmm_ral_access access);
   // There can only be one RAL Access on a RAL model
   if (this.ral_access != null && this.ral_access != access) begin
      `vmm_fatal(this.log, $psprintf("Memory %s is already used by another RAL access instance", this.get_fullname()));
   end
   this.ral_access = access;
endfunction: Xregister_ral_accessX


function string vmm_ral_mem::get_name();
   get_name = this.name;
endfunction: get_name


function string vmm_ral_mem::get_fullname();
   vmm_ral_block blk;

   get_fullname = this.get_name();

   // Do not include top-level name in full name
   blk = this.get_block();
   if (blk == null) return get_fullname;
   if (blk.get_parent() == null) return get_fullname;

   get_fullname = {this.parent.get_fullname(), ".", get_fullname};
endfunction: get_fullname


function int vmm_ral_mem::get_n_domains();
   get_n_domains = this.domains.size();
endfunction: get_n_domains


function void vmm_ral_mem::get_domains(ref string domains[]);
   domains = new [this.domains.size()] (this.domains);
endfunction: get_domains


function vmm_ral::access_e vmm_ral_mem::get_access(string domain = "");
   get_access = this.access;
   if (this.get_n_domains() == 1) return get_access;

   // Is the memory restricted in this domain?
   case (this.get_rights(domain))
     vmm_ral::RW:
       // No restrictions
       return get_access;

     vmm_ral::RO:
       case (get_access)
         vmm_ral::RW,
         vmm_ral::RO: get_access = vmm_ral::RO;

         vmm_ral::WO: begin
            `vmm_error(this.log,
                       $psprintf("WO memory %s restricted to RO in domain \"%s\"",
                                 this.get_fullname(), domain));
         end

         default:
           `vmm_error(this.log,
                      $psprintf("Invalid memory %s access mode \"%s\"",
                                this.get_fullname(), get_access.name()));
       endcase

     vmm_ral::WO:
       case (get_access)
         vmm_ral::RW,
         vmm_ral::WO: get_access = vmm_ral::WO;

         vmm_ral::RO: begin
            `vmm_error(this.log,
                       $psprintf("RO memory %s restricted to WO in domain \"%s\"",
                                 this.get_fullname(), get_access.name(), domain));
         end

         default:
           `vmm_error(this.log,
                      $psprintf("Invalid memory %s access mode \"%s\"",
                                this.get_fullname(), get_access.name()));
       endcase

     default:
       `vmm_error(this.log,
                  $psprintf("Shared memory \"%s\" is not shared in domain \"%s\"",
                            this.get_fullname(), domain));
   endcase
endfunction: get_access


function vmm_ral_access vmm_ral_mem::Xget_ral_accessX();
endfunction


function vmm_ral::access_e vmm_ral_mem::get_rights(string domain = "");
   int i;

   // No right restrictions if not shared
   if (this.domains.size() == 1) begin
      return vmm_ral::RW;
   end

   i = this.get_domain_index(domain);
   if (i < 0) return vmm_ral::RW;

   get_rights = this.rights[i];
endfunction: get_rights


function void vmm_ral_mem::get_virtual_fields(ref vmm_ral_vfield fields[]);
  vmm_ral_vfield vfields[];

  fields = new[0];
  `foreach (this.XvregsX,i) begin
    int n = fields.size();
    this.XvregsX[i].get_fields(vfields);
    fields = new[n + vfields.size()] (fields);
    foreach(vfields[j]) begin
      fields[n+j] = vfields[j];
    end
  end
endfunction: get_virtual_fields


// Return first occurrence of vfield matching name
function vmm_ral_vfield vmm_ral_mem::get_virtual_field_by_name(string name);
  vmm_ral_vfield vfields[];

  this.get_virtual_fields(vfields);
  foreach (vfields[i]) begin
    if (vfields[i].get_name() == name) return vfields[i];
  end
  `vmm_warning(this.log,
               $psprintf("Unable to find virtual field \"%s\" in memory %s.",
                         name, this.get_fullname()));
   return null;
endfunction: get_virtual_field_by_name


function void vmm_ral_mem::get_virtual_registers(ref vmm_ral_vreg regs[]);
  regs = new[this.XvregsX.size()];
  `foreach (this.XvregsX,i) begin
     regs[i] = this.XvregsX[i];
  end
endfunction: get_virtual_registers


function vmm_ral_vreg vmm_ral_mem::get_vreg_by_name(string name);
  `foreach (this.XvregsX,i) begin
    if (this.XvregsX[i].get_name() == name) return this.XvregsX[i];
  end
  `vmm_warning(this.log,
               $psprintf("Unable to find virtual register \"%s\" in memory %s.",
                         name, this.get_fullname()));

endfunction: get_vreg_by_name


function vmm_ral_vreg vmm_ral_mem::get_vreg_by_offset(bit [63:0] offset,
                                                      string domain = "");
   `vmm_error(this.log, "vmm_ral_mem::get_vreg_by_offset() not yet implemented");
   return null;
endfunction: get_vreg_by_offset


function vmm_ral_block vmm_ral_mem::get_block();
   get_block = this.parent;
endfunction: get_block


function bit [`VMM_RAL_ADDR_WIDTH-1:0] vmm_ral_mem::get_offset_in_block(bit [`VMM_RAL_ADDR_WIDTH-1:0] mem_addr = 0,
                                                                        string                        domain = "");
   `foreach (this.domains,i) begin
      if (this.domains[i] == domain) begin
         if (this.offset_in_block[i] === 'x) begin
            `vmm_warning(this.log, $psprintf("Memory \"%s\" is unmapped in domain \"%s\".", this.get_name(), domain));
            return '0;
         end
         
         return this.offset_in_block[i];
      end
   end
   `vmm_warning(this.log, $psprintf("Unable to find offset within domain \"%s\" in memory %s.",
                                    domain, this.get_fullname()));
   get_offset_in_block = '1;
endfunction: get_offset_in_block


function bit [`VMM_RAL_ADDR_WIDTH-1:0] vmm_ral_mem::get_address_in_system(bit [`VMM_RAL_ADDR_WIDTH-1:0] mem_addr = 0,
                                                       string                                           domain = "");
   bit [`VMM_RAL_ADDR_WIDTH-1:0] addr[];
         
   int i = this.get_domain_index(domain);
   if (i < 0) return 0;
         
   if (this.ral_access == null) begin
      `vmm_fatal(this.parent.log,
                 "RAL model is not associated with an access transactor");
      return 0;
   end
         
   if (this.offset_in_block[i] === 'x) begin
      `vmm_error(this.log, $psprintf("Memory \"%s\" is unmapped in domain \"%s\".", this.get_name(), this.domains[i]));
      return '1;
   end
         
   void'(this.ral_access.Xget_physical_addressesX(this.offset_in_block[i],
                                                  mem_addr, this.get_n_bytes(),
                                                  this.parent,
                                                  this.domains[i],
                                                  addr));

   get_address_in_system = addr[0];
endfunction: get_address_in_system


function longint unsigned vmm_ral_mem::get_size();
   get_size = this.size;
endfunction: get_size


function int unsigned vmm_ral_mem::get_n_bits();
   get_n_bits = this.n_bits;
endfunction: get_n_bits


function int unsigned vmm_ral_mem::get_n_bytes();
   get_n_bytes = (this.n_bits - 1) / 8 + 1;
endfunction: get_n_bytes


function void vmm_ral_mem::display(string prefix = "",
                                   string domain = "");
   $write("%s\n", this.psdisplay(prefix, domain));
endfunction: display


function string vmm_ral_mem::psdisplay(string prefix = "",
                                       string domain = "");
   $sformat(psdisplay, "%sMemory %s -- %0dx%0d bits @", prefix,
            this.get_fullname(), this.get_size(), this.get_n_bits());
   `foreach (this.domains,i) begin
      if (this.domains[i] == domain) begin
         if (this.offset_in_block[i] === 'x) begin
            psdisplay = {psdisplay, "none"};
         end
         else begin
            $sformat(psdisplay, "%s'h%h", psdisplay,
                     this.get_address_in_system(0, domain));
         end
         break;
      end
   end
endfunction: psdisplay


function void vmm_ral_mem::set_attribute(string name,
                                         string value);
   if (name == "") begin
      `vmm_error(this.log, $psprintf("Cannot set anonymous attribute \"\" in memory \"%s\". Please specify an attribute name.",
                                       name, this.get_fullname()));
      return;
   end

   if (this.attributes.exists(name)) begin
      if (value != "") begin
         `vmm_warning(this.log, $psprintf("Redefining attributed \"%s\" in memory \"%s\" to \"%s\".",
                                          name, this.get_fullname(), value));
         this.attributes[name] = value;
      end
      else begin
         this.attributes.delete(name);
      end
      return;
   end

   if (value == "") begin
      `vmm_warning(this.log, $psprintf("Attempting to delete non-existent attribute \"%s\" in memory \"%s\".",
                                       name, this.get_fullname()));
      return;
   end

   this.attributes[name] = value;
endfunction: set_attribute


function string vmm_ral_mem::get_attribute(string name,
                                           bit inherited = 1);
   if (this.attributes.exists(name)) begin
      return this.attributes[name];
   end

   if (inherited) return this.parent.get_attribute(name);

   return "";
endfunction: get_attribute


function void vmm_ral_mem::get_all_attributes(ref string names[],
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


function void vmm_ral_mem::ral_power_down();
   this.is_powered_down = 1;
endfunction: ral_power_down


function void vmm_ral_mem::ral_power_up();
   this.is_powered_down = 0;
endfunction: ral_power_up


function bit vmm_ral_mem::can_cover(int models);
   return ((this.has_cover & models) == models);
endfunction: can_cover


function int vmm_ral_mem::set_cover(int is_on);
   if (is_on == vmm_ral::NO_COVERAGE) begin
      this.cover_on = is_on;
      return this.cover_on;
   end

   if (is_on & vmm_ral::ADDR_MAP) begin
      if (this.has_cover & vmm_ral::ADDR_MAP) begin
          this.cover_on |= vmm_ral::ADDR_MAP;
      end else begin
          `vmm_warning(this.log, $psprintf("\"%s\" - Cannot turn ON Address Map coverage becasue the corresponding coverage model was not generated.", this.get_fullname()));
      end
   end else begin
      return this.cover_on;
   end

   set_cover = this.cover_on;
endfunction: set_cover


function bit vmm_ral_mem::is_cover_on(int is_on = vmm_ral::ALL_COVERAGE);
   if (this.can_cover(is_on) == 0) return 0;
   return ((this.cover_on & is_on) == is_on);
endfunction: is_cover_on


task vmm_ral_mem::init(output bit                           is_ok,
                       input  init_e                        pattern,
                       input  bit [`VMM_RAL_DATA_WIDTH-1:0] data);
   int incr;
   is_ok = 0;

   if (this.backdoor == null) begin
      `vmm_error(this.log, $psprintf("No backdoor available to initialize memory %s", this.get_fullname()));
      return;
   end

   case (pattern)
   UNKNOWNS:
     begin
        data = 'x;
        incr = 0;
     end

   ZEROES:
     begin
        data = '0;
        incr = 0;
     end

   ONES:
     begin
        data = '1;
        incr = 0;
     end

   VALUE:
     begin
        incr = 0;
     end

   INCR:
     begin
        incr = 1;
     end

   DECR:
     begin
        incr = -1;
     end
   endcase

   // ToDo...
endtask:init


task vmm_ral_mem::write(output vmm_rw::status_e              status,
                        input  bit [`VMM_RAL_ADDR_WIDTH-1:0] mem_addr,
                        input  bit [`VMM_RAL_DATA_WIDTH-1:0] value,
                        input  vmm_ral::path_e               path = vmm_ral::DEFAULT,
                        input  string                        domain = "",
                        input  int                           data_id = -1,
                        input  int                           scenario_id = -1,
                        input  int                           stream_id = -1);
   status = vmm_rw::ERROR;
   
   if (this.ral_access == null) begin
      `vmm_error(this.log, $psprintf("Memory %s not associated with RAL access object", this.get_fullname()));
      return;
   end
   
   if (this.is_powered_down) begin
      `vmm_error(this.log, $psprintf("Memory %s cannot be accessed when it is powered down", this.get_fullname()));
      return;
   end

   if (path == vmm_ral::DEFAULT) path = this.parent.get_default_access();

   `vmm_callback(vmm_ral_mem_callbacks,
                 pre_write(this, mem_addr, value, path, domain));

   if (path == vmm_ral::DEFAULT) path = this.parent.get_default_access();

   if (path == vmm_ral::BACKDOOR &&
       this.backdoor == null) begin
      `vmm_warning(this.log, $psprintf("No backdoor access available for memory \"%s\". Using frontdoor instead.", this.get_name()));
      path = vmm_ral::BFM;
   end

   case (path)
      
      vmm_ral::BFM: begin
         int di = this.get_domain_index(domain);
         if (di < 0) return;

         if (this.frontdoor[di] != null) begin
            this.frontdoor[di].write(status, mem_addr, value,
                                     data_id, scenario_id, stream_id);
         end
         else begin
            bit [`VMM_RAL_ADDR_WIDTH-1:0] addr[];
            int w, j;
            int n_bits;
         
            if (this.offset_in_block[di] === 'x) begin
               `vmm_error(this.log, $psprintf("Memory \"%s\" unmapped in domain \"%s\" does not have a user-defined frontdoor",
                                              this.get_name(),
                                              this.domains[di]));
               return;
            end
         
            w = this.ral_access.Xget_physical_addressesX(this.offset_in_block[di],
                                                         mem_addr,
                                                         this.get_n_bytes(),
                                                         this.parent,
                                                         this.domains[di],
                                                         addr);
            j = 0;
            n_bits = this.get_n_bits();
            foreach (addr[i]) begin
               bit [`VMM_RAL_DATA_WIDTH-1:0] data;
               data = value >> (j*8);
               this.ral_access.write(status, addr[i], data,
                                     (n_bits > w*8) ? w*8 : n_bits,
                                     this.parent.get_external_domain(this.domains[di]),
                                     data_id, scenario_id, stream_id);
               if (status != vmm_rw::IS_OK) break;
               j += w;
               n_bits -= w * 8;
            end
         end

         if (this.cover_on) 
            this.parent.XsampleX(this.offset_in_block[di] + 
               mem_addr * (((this.get_n_bytes()-1)/this.parent.get_n_bytes(domain))+1), di);
      end
      
      vmm_ral::BACKDOOR: begin
         // Mimick front door access: Do not write read-only memories
         if (this.get_access(domain) == vmm_ral::RW) begin
            this.poke(status, mem_addr, value,
                      data_id, scenario_id, stream_id);
         end else status = vmm_rw::IS_OK;
      end
   endcase

   `vmm_callback(vmm_ral_mem_callbacks,
                 post_write(this, mem_addr, value, path, domain, status));

   `vmm_trace(this.log, $psprintf("Wrote memory \"%s\"[%0d] via %s: with 'h%h",
                                  this.get_fullname(), mem_addr,
                                  (path == vmm_ral::BFM) ? "frontdoor" : "backdoor",
                                  value));
endtask: write


task vmm_ral_mem::read(output vmm_rw::status_e              status,
                       input  bit [`VMM_RAL_ADDR_WIDTH-1:0] mem_addr,
                       output bit [`VMM_RAL_DATA_WIDTH-1:0] value,
                       input  vmm_ral::path_e               path = vmm_ral::DEFAULT,
                       input  string                        domain = "",
                       input  int                           data_id = -1,
                       input  int                           scenario_id = -1,
                       input  int                           stream_id = -1);
   status = vmm_rw::ERROR;
   
   if (this.ral_access == null) begin
      `vmm_error(this.log, $psprintf("Memory %s not associated with RAL access object", this.get_fullname()));
      return;
   end
   
   if (this.is_powered_down) begin
      `vmm_error(this.log, $psprintf("Memory %s cannot be accessed when it is powered down", this.get_fullname()));
      return;
   end

   if (path == vmm_ral::DEFAULT) path = this.parent.get_default_access();

   `vmm_callback(vmm_ral_mem_callbacks,
                 pre_read(this, mem_addr, path, domain));

   if (path == vmm_ral::DEFAULT) path = this.parent.get_default_access();

   if (path == vmm_ral::BACKDOOR &&
       this.backdoor == null) begin
      `vmm_warning(this.log, $psprintf("No backdoor access available for memory \"%s\". Using frontdoor instead.", this.get_name()));
      path = vmm_ral::BFM;
   end

   case (path)
      
      vmm_ral::BFM: begin
         int di = this.get_domain_index(domain);
         if (di < 0) return;
         
         if (this.frontdoor[di] != null) begin
            this.frontdoor[di].read(status, mem_addr, value,
                                   data_id, scenario_id, stream_id);
         end
         else begin
            bit [`VMM_RAL_ADDR_WIDTH-1:0] addr[];
            int w, j;
            int n_bits;
         
            if (this.offset_in_block[di] === 'x) begin
               `vmm_error(this.log, $psprintf("Memory \"%s\" unmapped in domain \"%s\" does not have a user-defined frontdoor",
                                              this.get_name(),
                                              this.domains[di]));
               return;
            end
         
            w = this.ral_access.Xget_physical_addressesX(this.offset_in_block[di],
                                                         mem_addr,
                                                         this.get_n_bytes(),
                                                         this.parent,
                                                         this.domains[di],
                                                         addr);
            j = 0;
            n_bits = this.get_n_bits();
            value = 0;
            foreach (addr[i]) begin
               bit [`VMM_RAL_DATA_WIDTH-1:0] data;
               this.ral_access.read(status, addr[i], data,
                                    (n_bits > w*8) ? w*8 : n_bits,
                                    this.parent.get_external_domain(this.domains[di]),
                                    data_id, scenario_id, stream_id);
               if (status != vmm_rw::IS_OK) break;
               value |= (data & ((1 << (w*8)) - 1)) << (j*8);
               j += w;
               n_bits -= w * 8;
            end
         end

         if (this.cover_on) 
            this.parent.XsampleX(this.offset_in_block[di] + 
               mem_addr * (((this.get_n_bytes()-1)/this.parent.get_n_bytes(domain))+1), di);
      end
      
      vmm_ral::BACKDOOR: begin
         this.peek(status, mem_addr, value,
                   data_id, scenario_id, stream_id);
      end
   endcase

   `vmm_callback(vmm_ral_mem_callbacks,
                 post_read(this, mem_addr, value, path, domain, status));

   `vmm_trace(this.log, $psprintf("Read memory \"%s\"[%0d] via %s: 'h%h",
                                  this.get_fullname(), mem_addr,
                                  (path == vmm_ral::BFM) ? "frontdoor" : "backdoor",
                                  value));
endtask: read


function bit vmm_ral_mem::validate_burst(vmm_ral_mem_burst burst);
   if (burst.start_offset >= this.get_size()) begin
      `vmm_error(this.log, $psprintf("Starting burst offset 'h%0h is greater than number of memory locations ('h%0h)",
                                     burst.start_offset, this.get_size()));
      return 0;
   end

   if (burst.max_offset >= this.get_size()) begin
      `vmm_error(this.log, $psprintf("Maximum burst offset 'h%0h is greater than number of memory locations ('h%0h)",
                                     burst.max_offset, this.get_size()));
      return 0;
   end

   if (burst.n_beats == 0) begin
      `vmm_error(this.log, "Zero-length burst");
      return 0;
   end

   if (burst.start_offset > burst.max_offset) begin
      `vmm_error(this.log, $psprintf("Starting burst offset ('h%0h) greater than maximum burst offset ('h%0h)",
                                     burst.start_offset, burst.max_offset));
      return 0;
   end

   if (burst.n_beats > 1 &&
       burst.start_offset + burst.incr_offset >= burst.max_offset) begin
      `vmm_error(this.log, $psprintf("First burst offset increment 'h%0h+%0h is greater than maximum burst offset ('h%0h)",
                                     burst.start_offset, burst.incr_offset,
                                     burst.max_offset));
      return 0;
   end

   return 1;
endfunction: validate_burst


task vmm_ral_mem::burst_write(output vmm_rw::status_e              status,
                              input  vmm_ral_mem_burst             burst,
                              input  bit [`VMM_RAL_DATA_WIDTH-1:0] value[],
                              input  vmm_ral::path_e               path = vmm_ral::DEFAULT,
                              input  string                        domain = "",
                              input  int                           data_id = -1,
                              input  int                           scenario_id = -1,
                              input  int                           stream_id = -1);
   status = vmm_rw::ERROR;

   if (this.ral_access == null) begin
      `vmm_error(this.log, $psprintf("Memory %s not associated with RAL access object", this.get_fullname()));
      return;
   end
   
   if (this.is_powered_down) begin
      `vmm_error(this.log, $psprintf("Memory %s cannot be accessed when it is powered down", this.get_fullname()));
      return;
   end

   if (path == vmm_ral::DEFAULT) path = this.parent.get_default_access();

   `vmm_callback(vmm_ral_mem_callbacks,
                 pre_burst(this, vmm_rw::WRITE, burst, value, path, domain));

   if (!this.validate_burst(burst)) return;

   if (path == vmm_ral::DEFAULT) path = this.parent.get_default_access();

   case (path)
      
      vmm_ral::BFM: begin
         int di = this.get_domain_index(domain);
         if (di < 0) return;

         if (this.frontdoor[di] != null) begin
            this.frontdoor[di].burst_write(status, burst, value,
                                           data_id, scenario_id, stream_id);
         end
         else begin
            bit [`VMM_RAL_ADDR_WIDTH-1:0] addr[];
            int w;
            int n_bits;
         
            if (this.offset_in_block[di] === 'x) begin
               `vmm_error(this.log, $psprintf("Memory \"%s\" unmapped in domain \"%s\" does not have a user-defined frontdoor",
                                              this.get_name(),
                                              this.domains[di]));
               return;
            end
         
            w = this.ral_access.Xget_physical_addressesX(this.offset_in_block[di],
                                                         burst.start_offset,
                                                         this.get_n_bytes(),
                                                         this.parent,
                                                         this.domains[di],
                                                         addr);
            n_bits = this.get_n_bits();
            // Cannot burst memory through a narrower datapath
            if (n_bits > w*8) begin
               `vmm_error(this.log, $psprintf("Cannot burst-write a %0d-bit memory through a narrower data path (%0d bytes)",
                                              n_bits, w));
               return;
            end
            // Translate offsets into addresses
            begin
               bit [`VMM_RAL_ADDR_WIDTH-1:0] start, incr, max;

               start = addr[0];

               w = this.ral_access.Xget_physical_addressesX(this.offset_in_block[di],
                                                            burst.start_offset + burst.incr_offset,
                                                            this.get_n_bytes(),
                                                            this.parent,
                                                            this.domains[di],
                                                            addr);
               incr = addr[0] - start;

               w = this.ral_access.Xget_physical_addressesX(this.offset_in_block[di],
                                                            burst.max_offset,
                                                            this.get_n_bytes(),
                                                            this.parent,
                                                            this.domains[di],
                                                            addr);

               max = addr[addr.size()-1];

               this.ral_access.burst_write(status, start, incr, max, value,
                                           burst.user_data, n_bits,
                                           this.parent.get_external_domain(this.domains[di]),
                                           data_id, scenario_id, stream_id);
            end
         end

         if (this.cover_on) begin
            bit [`VMM_RAL_ADDR_WIDTH-1:0] addr;
            for (addr = burst.start_offset;
                 addr <= burst.max_offset;
                 addr += burst.incr_offset) begin
               this.parent.XsampleX(this.offset_in_block[di] + addr, di);
            end
         end
      end
      
      vmm_ral::BACKDOOR: begin
         // Mimick front door access: Do not write read-only memories
         if (this.get_access(domain) == vmm_ral::RW) begin
            bit [`VMM_RAL_ADDR_WIDTH-1:0] addr;
            addr = burst.start_offset;
            foreach (value[i]) begin
               this.poke(status, addr, value[i],
                         data_id, scenario_id, stream_id);
               if (status != vmm_rw::IS_OK) return;
               addr += burst.incr_offset;
               if (addr > burst.max_offset) begin
                  addr -= (burst.max_offset - burst.start_offset - 1);
               end
            end
         end
         else status = vmm_rw::IS_OK;
      end
   endcase

   `vmm_callback(vmm_ral_mem_callbacks,
                 post_burst(this, vmm_rw::WRITE, burst, value,
                            path, domain, status));
endtask: burst_write


task vmm_ral_mem::burst_read(output vmm_rw::status_e              status,
                             input  vmm_ral_mem_burst             burst,
                             output bit [`VMM_RAL_DATA_WIDTH-1:0] value[],
                             input  vmm_ral::path_e               path = vmm_ral::DEFAULT,
                             input  string                        domain = "",
                             input  int                           data_id = -1,
                             input  int                           scenario_id = -1,
                             input  int                           stream_id = -1);
   status = vmm_rw::ERROR;

   if (this.ral_access == null) begin
      `vmm_error(this.log, $psprintf("Memory %s not associated with RAL access object", this.get_fullname()));
      return;
   end
   
   if (this.is_powered_down) begin
      `vmm_error(this.log, $psprintf("Memory %s cannot be accessed when it is powered down", this.get_fullname()));
      return;
   end

   if (path == vmm_ral::DEFAULT) path = this.parent.get_default_access();

   begin
      bit [`VMM_RAL_DATA_WIDTH-1:0] junk[];

      `vmm_callback(vmm_ral_mem_callbacks,
                    pre_burst(this, vmm_rw::READ, burst, junk, path, domain));
   end

   if (!this.validate_burst(burst)) return;

   if (path == vmm_ral::DEFAULT) path = this.parent.get_default_access();

   case (path)
      
      vmm_ral::BFM: begin
         int di = this.get_domain_index(domain);
         if (di < 0) return;
         
         if (this.frontdoor[di] != null) begin
            this.frontdoor[di].burst_read(status, burst, value,
                                          data_id, scenario_id, stream_id);
         end
         else begin
            bit [`VMM_RAL_ADDR_WIDTH-1:0] addr[];
            int n_bits, w;
         
            if (this.offset_in_block[di] === 'x) begin
               `vmm_error(this.log, $psprintf("Memory \"%s\" unmapped in domain \"%s\" does not have a user-defined frontdoor",
                                              this.get_name(),
                                              this.domains[di]));
               return;
            end
         
            w = this.ral_access.Xget_physical_addressesX(this.offset_in_block[di],
                                                         burst.start_offset,
                                                         this.get_n_bytes(),
                                                         this.parent,
                                                         this.domains[di],
                                                         addr);
            n_bits = this.get_n_bits();
            // Cannot burst memory through a narrower datapath
            if (n_bits > w*8) begin
               `vmm_error(this.log, $psprintf("Cannot burst-write a %0d-bit memory through a narrower data path (%0d bytes)",
                                              n_bits, w));
               return;
            end
            // Translate the offset-based burst into address-based burst
            begin
               bit [`VMM_RAL_ADDR_WIDTH-1:0] start, incr, max;

               start = addr[0];

               w = this.ral_access.Xget_physical_addressesX(this.offset_in_block[di],
                                                            burst.start_offset + burst.incr_offset,
                                                            this.get_n_bytes(),
                                                            this.parent,
                                                            this.domains[di],
                                                            addr);
               incr = addr[0] - start;

               w = this.ral_access.Xget_physical_addressesX(this.offset_in_block[di],
                                                            burst.max_offset,
                                                            this.get_n_bytes(),
                                                            this.parent,
                                                            this.domains[di],
                                                            addr);

               max = addr[addr.size()-1];

               this.ral_access.burst_read(status, start, incr, max,
                                          burst.n_beats, value,
                                          burst.user_data, n_bits,
                                          this.parent.get_external_domain(this.domains[di]),
                                          data_id, scenario_id, stream_id);
            end
         end

         if (this.cover_on) begin
            bit [`VMM_RAL_ADDR_WIDTH-1:0] addr;
            for (addr = burst.start_offset;
                 addr <= burst.max_offset;
                 addr += burst.incr_offset) begin
               this.parent.XsampleX(this.offset_in_block[di] + addr, di);
            end
         end
      end
      
      vmm_ral::BACKDOOR: begin
         bit [`VMM_RAL_ADDR_WIDTH-1:0] addr;
         value = new [burst.n_beats];
         addr = burst.start_offset;
         foreach (value[i]) begin
            this.peek(status, addr, value[i],
                      data_id, scenario_id, stream_id);
            if (status != vmm_rw::IS_OK) return;
            addr += burst.incr_offset;
            if (addr > burst.max_offset) begin
               addr -= (burst.max_offset - burst.start_offset - 1);
            end
         end
      end
   endcase

   `vmm_callback(vmm_ral_mem_callbacks,
                 post_burst(this, vmm_rw::READ, burst, value,
                            path, domain, status));
endtask: burst_read


task vmm_ral_mem::poke(output vmm_rw::status_e              status,
                       input  bit [`VMM_RAL_ADDR_WIDTH-1:0] mem_addr,
                       input  bit [`VMM_RAL_DATA_WIDTH-1:0] value,
                       input  int                           data_id = -1,
                       input  int                           scenario_id = -1,
                       input  int                           stream_id = -1);
   if (this.backdoor == null) begin
      `vmm_error(this.log, $psprintf("No backdoor access available in memory %s", this.get_fullname()));
      status = vmm_rw::ERROR;
      return;
   end
   if (this.is_powered_down) begin
      `vmm_error(this.log, $psprintf("Memory %s cannot be accessed when it is powered down", this.get_fullname()));
      return;
   end

   this.backdoor.write(status, mem_addr, value, data_id, scenario_id, stream_id);

   `vmm_trace(this.log, $psprintf("Poked memory \"%s\"[%0d] with: 'h%h",
                                  this.get_fullname(), mem_addr, value));
endtask: poke


task vmm_ral_mem::peek(output vmm_rw::status_e              status,
                       input  bit [`VMM_RAL_ADDR_WIDTH-1:0] mem_addr,
                       output bit [`VMM_RAL_DATA_WIDTH-1:0] value,
                       input  int                           data_id = -1,
                       input  int                           scenario_id = -1,
                       input  int                           stream_id = -1);
   if (this.backdoor == null) begin
      `vmm_error(this.log, $psprintf("No backdoor access available in memory %s", this.get_fullname()));
      status = vmm_rw::ERROR;
      return;
   end
   if (this.is_powered_down) begin
      `vmm_error(this.log, $psprintf("Memory %s cannot be accessed when it is powered down", this.get_fullname()));
      return;
   end

   this.backdoor.read(status, mem_addr, value, data_id, scenario_id, stream_id);

   `vmm_trace(this.log, $psprintf("Peeked memory \"%s\"[%0d]: 'h%h",
                                  this.get_fullname(), mem_addr, value));
endtask: peek


task vmm_ral_mem::readmemh(string filename);
endtask: readmemh


task vmm_ral_mem::writememh(string filename);
endtask: writememh


function void vmm_ral_mem::set_frontdoor(vmm_ral_mem_frontdoor ftdr,
                                         string                domain = "");
   `foreach(this.domains,i) begin
      if (this.domains[i] == domain) begin
         this.frontdoor[i] = ftdr;
         return;
      end
   end
   `vmm_error(this.log, $psprintf("Domain \"%s\" not found in memory %s", domain, this.get_fullname()));
endfunction: set_frontdoor


function vmm_ral_mem_frontdoor vmm_ral_mem::get_frontdoor(string domain = "");
   `foreach(this.domains,i) begin
      if (this.domains[i] == domain) begin
         return this.frontdoor[i];
      end
   end
   `vmm_error(this.log, $psprintf("Domain \"%s\" not found in memory %s", domain, this.get_fullname()));
endfunction: get_frontdoor


function void vmm_ral_mem::set_backdoor(vmm_ral_mem_backdoor bkdr);
   this.backdoor = bkdr;
endfunction: set_backdoor


function vmm_ral_mem_backdoor vmm_ral_mem::get_backdoor();
   get_backdoor = this.backdoor;
endfunction: get_backdoor


function void vmm_ral_mem::prepend_callback(vmm_ral_mem_callbacks cb);
   `foreach (this.callbacks,i) begin
      if (this.callbacks[i] == cb) begin
         `vmm_warning(this.log, $psprintf("Callback has already been registered with memory %s", this.get_fullname()));
         return;
      end
   end
   
   // Prepend new callback
   this.callbacks.push_front(cb);
endfunction: prepend_callback


function void vmm_ral_mem::append_callback(vmm_ral_mem_callbacks cb);
   `foreach (this.callbacks,i) begin
      if (this.callbacks[i] == cb) begin
         `vmm_warning(this.log, $psprintf("Callback has already been registered with memory %s", this.get_fullname()));
         return;
      end
   end
   
   // Append new callback
   this.callbacks.push_back(cb);
endfunction: append_callback


function void vmm_ral_mem::unregister_callback(vmm_ral_mem_callbacks cb);
   `foreach (this.callbacks,i) begin
      if (this.callbacks[i] == cb) begin
         int j = i;
         // Unregister it
         this.callbacks.delete(j);
         return;
      end
   end

`vmm_warning(this.log, $psprintf("Callback was not registered with memory %s", this.get_fullname()));
endfunction: unregister_callback


function int vmm_ral_mem::get_domain_index(string domain);
   // If the domain is "" and there is only one domain,
   // assume it is the one domain available to avoid
   // having to always have to specify domains
   if (domain == "" && this.domains.size() == 1) return 0;

   `foreach (this.domains,i) begin
      if (this.domains[i] == domain) return i;
   end
   `vmm_warning(this.log, $psprintf("Unknown domain name \"%s\" in memory %s.", domain, this.get_fullname()));
   return -1;
endfunction: get_domain_index


task vmm_ral_mem_frontdoor::write(output vmm_rw::status_e              status,
                                  input  bit [`VMM_RAL_ADDR_WIDTH-1:0] offset,
                                  input  bit [`VMM_RAL_DATA_WIDTH-1:0] data,
                                  input  int                           data_id = -1,
                                  input  int                           scenario_id = -1,
                                  input  int                           stream_id = -1);
   `vmm_fatal(this.log, "vmm_ral_mem_frontdoor::write() method has not been overloaded");
endtask: write


task vmm_ral_mem_frontdoor::read(output vmm_rw::status_e              status,
                                 input  bit [`VMM_RAL_ADDR_WIDTH-1:0] offset,
                                 output bit [`VMM_RAL_DATA_WIDTH-1:0] data,
                                 input  int                           data_id = -1,
                                 input  int                           scenario_id = -1,
                                 input  int                           stream_id = -1);
   `vmm_fatal(this.log, "vmm_ral_mem_frontdoor::read() method has not been overloaded");
endtask: read

task vmm_ral_mem_frontdoor::burst_write(output vmm_rw::status_e              status,
                                        input  vmm_ral_mem_burst             burst,
                                        input  bit [`VMM_RAL_DATA_WIDTH-1:0] data[],
                                        input  int                           data_id = -1,
                                        input  int                           scenario_id = -1,
                                        input  int                           stream_id = -1);
   `vmm_fatal(this.log, "vmm_ral_mem_frontdoor::burst_write() method has not been overloaded");
endtask

task vmm_ral_mem_frontdoor::burst_read(output vmm_rw::status_e              status,
                                       input  vmm_ral_mem_burst             burst,
                                       output bit [`VMM_RAL_DATA_WIDTH-1:0] data[],
                                       input  int                           data_id = -1,
                                       input  int                           scenario_id = -1,
                                       input  int                           stream_id = -1);
   `vmm_fatal(this.log, "vmm_ral_mem_frontdoor::burst_read() method has not been overloaded");
endtask


function int unsigned vmm_ral_mem::get_mem_ID();
   get_mem_ID =  this.mem_id;
endfunction

function vmm_ral_mem vmm_ral_get_mem_by_ID(int unsigned id);
   vmm_ral_mem m;
   if (m.all_mems.exists(id)) 
      vmm_ral_get_mem_by_ID = m.all_mems[id];
   else vmm_ral_get_mem_by_ID = null;
endfunction
