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


class vmm_ral_access extends `VMM_XACTOR;
   vmm_ral::path_e default_path = vmm_ral::BFM;  // Cannot be "DEFAULT"

   protected vmm_ral_block_or_sys model;
   
   protected vmm_rw_xactor rw_exec[string]; // One per domain

   extern function new();

   extern function void set_model(vmm_ral_block_or_sys model);
   extern function vmm_ral_block_or_sys get_model();
   extern function void add_xactor(vmm_rw_xactor xact,
                                   string        domain = "");

   extern task write(output vmm_rw::status_e status,
                     input  bit [`VMM_RAL_ADDR_WIDTH-1:0] addr,
                     input  bit [`VMM_RAL_DATA_WIDTH-1:0] data,
                     input  int                           n_bits = `VMM_RAL_DATA_WIDTH,
                     input  string                        domain = "",
                     input  int                           data_id = -1,
                     input  int                           scenario_id = -1,
                     input  int                           stream_id = -1);

   extern task read(output vmm_rw::status_e status,
                    input  bit [`VMM_RAL_ADDR_WIDTH-1:0] addr,
                    output bit [`VMM_RAL_DATA_WIDTH-1:0] data,
                     input  int                           n_bits = `VMM_RAL_DATA_WIDTH,
                    input  string                         domain = "",
                    input  int                            data_id = -1,
                    input  int                            scenario_id = -1,
                    input  int                            stream_id = -1);

   extern task burst_write(output vmm_rw::status_e              status,
                           input  bit [`VMM_RAL_ADDR_WIDTH-1:0] start,
                           input  bit [`VMM_RAL_ADDR_WIDTH-1:0] incr,
                           input  bit [`VMM_RAL_ADDR_WIDTH-1:0] max,
                           input  bit [`VMM_RAL_DATA_WIDTH-1:0] data[],
                           input  vmm_data                      user = null,
                           input  int                           n_bits = `VMM_RAL_DATA_WIDTH,
                           input  string                        domain = "",
                           input  int                           data_id = -1,
                           input  int                           scenario_id = -1,
                           input  int                           stream_id = -1);

   extern task burst_read(output vmm_rw::status_e              status,
                          input  bit [`VMM_RAL_ADDR_WIDTH-1:0] start,
                          input  bit [`VMM_RAL_ADDR_WIDTH-1:0] incr,
                          input  bit [`VMM_RAL_ADDR_WIDTH-1:0] max,
                          input  int                           n_beats,
                          output bit [`VMM_RAL_DATA_WIDTH-1:0] data[],
                          input  vmm_data                      user = null,
                          input  int                           n_bits = `VMM_RAL_DATA_WIDTH,
                          input  string                        domain = "",
                          input  int                           data_id = -1,
                          input  int                           scenario_id = -1,
                          input  int                           stream_id = -1);

   extern virtual function bit set_by_name(input string                        name,
                                           input bit [`VMM_RAL_DATA_WIDTH-1:0] value);
   extern virtual function bit get_by_name(input  string                        name,
                                           output bit [`VMM_RAL_DATA_WIDTH-1:0] value);

   extern task write_by_name(output vmm_rw::status_e              status,
                             input  string                        name,
                             input  bit [`VMM_RAL_DATA_WIDTH-1:0] data,
                             input  vmm_ral::path_e               path   = vmm_ral::DEFAULT,
                             input  string                        domain = "",
                             input  int                           data_id = -1,
                             input  int                           scenario_id = -1,
                             input  int                           stream_id = -1);

   extern task read_by_name(output vmm_rw::status_e              status,
                            input  string                        name,
                            output bit [`VMM_RAL_DATA_WIDTH-1:0] data,
                            input  vmm_ral::path_e               path   = vmm_ral::DEFAULT,
                            input  string                        domain = "",
                            input  int                           data_id = -1,
                            input  int                           scenario_id = -1,
                            input  int                           stream_id = -1);

   extern task write_mem_by_name(output vmm_rw::status_e              status,
                                 input  string                        name,
                                 input  bit [`VMM_RAL_ADDR_WIDTH-1:0] offset,
                                 input  bit [`VMM_RAL_DATA_WIDTH-1:0] data,
                                 input  vmm_ral::path_e               path   = vmm_ral::DEFAULT,
                                 input  string                        domain = "",
                                 input  int                           data_id = -1,
                                 input  int                           scenario_id = -1,
                                 input  int                           stream_id = -1);   

   extern task read_mem_by_name(output vmm_rw::status_e status,
                                input  string                        name,
                                input  bit [`VMM_RAL_ADDR_WIDTH-1:0] offset,
                                output bit [`VMM_RAL_DATA_WIDTH-1:0] data,
                                input  vmm_ral::path_e               path = vmm_ral::DEFAULT,
                                input  string                        domain = "",
                                input  int                           data_id = -1,
                                input  int                           scenario_id = -1,
                                input  int                           stream_id = -1);

   /*local*/ extern function int
     Xget_physical_addressesX(bit [`VMM_RAL_ADDR_WIDTH-1:0]     base_addr,
                              bit [`VMM_RAL_ADDR_WIDTH-1:0]     mem_offset,
                              int unsigned                      n_bytes,
                              vmm_ral_block_or_sys              in_block,
                              string                            domain,
                              ref bit [`VMM_RAL_ADDR_WIDTH-1:0] addr[]);
endclass: vmm_ral_access


function vmm_ral_access::new();
   super.new("RVM RAL Access", "Main");
endfunction: new


function void vmm_ral_access::set_model(vmm_ral_block_or_sys model);
   if (this.model != null) begin
      `vmm_error(this.log, "A RAL abstraction model has already been associated with this RAL access interface");
      return;
   end

   this.model = model;

   // Register this RAL access object with the RAL model
   model.Xregister_ral_accessX(this);
endfunction: set_model


function vmm_ral_block_or_sys vmm_ral_access::get_model();
   get_model = this.model;
endfunction: get_model


function void vmm_ral_access::add_xactor(vmm_rw_xactor xact,
                                         string        domain = "");
   if (this.model == null) begin
      `vmm_error(this.log, "A RAL abstraction model has not yet been associated with this RAL access interface");
      return;
   end

   if(xact == null) begin
      `vmm_error(this.log, "Null argument provided for RW Xactor");
      return;
   end

   // Check if the specified domain matches a domain in the model
   begin
      string domains[];
      bit found = 0;

      model.get_domains(domains);
      foreach (domains[i]) begin
         if (domains[i] == domain) begin
            found = 1;
            break;
         end
      end
      if (!found) begin
         `vmm_error(this.log, $psprintf("Domain \"%s\" does not exist in RAL model",
                                        domain));
         if (this.log.start_msg(vmm_log::FAILURE_TYP, vmm_log::ERROR_SEV)) begin
            string msg;
            void'(this.log.text($psprintf("Domain \"%s\" does not exist in RAL model \"%s\"",
                                          domain, this.model.get_name())));
            msg = "Available domains are:";
            foreach (domains[i]) begin
               $sformat(msg, "%s \"%s\"", msg, domains[i]);
            end
            void'(this.log.text(msg));
            this.log.end_msg();
         end
         return;
      end
   end

   if (this.rw_exec.exists(domain)) begin
      `vmm_error(this.log, $psprintf("Transactor for domain \"%s\" already exists",
                                     domain));
   end
   else begin
      this.rw_exec[domain] = xact;

      // Make sure transactor is started
      xact.start_xactor();
   end
endfunction: add_xactor


task vmm_ral_access::write(output vmm_rw::status_e              status,
                           input  bit [`VMM_RAL_ADDR_WIDTH-1:0] addr,
                           input  bit [`VMM_RAL_DATA_WIDTH-1:0] data,
                           input  int                           n_bits = `VMM_RAL_DATA_WIDTH,
                           input  string                        domain = "",
                           input  int                           data_id = -1,
                           input  int                           scenario_id = -1,
                           input  int                           stream_id = -1);
   status = vmm_rw::ERROR;
   
   if (!this.rw_exec.exists(domain)) begin
      `vmm_error(this.log, $psprintf("No transactor available to physically access domain \"%s\".",
                                     domain));
      return;
   end

   `vmm_trace(this.log, $psprintf("Writing 'h%h at 'h%h via domain \"%s\"...",
                                  data, addr, domain));

   begin
      vmm_rw_access rw = new;

      rw.data_id     = data_id;
      rw.scenario_id = scenario_id;
      rw.stream_id   = stream_id;

      rw.kind = vmm_rw::WRITE;
      rw.addr = addr;
      rw.data = data;
      rw.n_bits = n_bits;
      this.rw_exec[domain].exec_chan.put(rw);
      rw.notify.wait_for(vmm_data::ENDED);
      status = rw.status;
   end
endtask: write


task vmm_ral_access::read(output vmm_rw::status_e              status,
                          input  bit [`VMM_RAL_ADDR_WIDTH-1:0] addr,
                          output bit [`VMM_RAL_DATA_WIDTH-1:0] data,
                          input  int                           n_bits = `VMM_RAL_DATA_WIDTH,
                          input  string                        domain = "",
                          input  int                           data_id = -1,
                          input  int                           scenario_id = -1,
                          input  int                           stream_id = -1);
   status = vmm_rw::ERROR;
   
   if (!this.rw_exec.exists(domain)) begin
      `vmm_error(this.log, $psprintf("No transactor available to physically access domain \"%s\".",
                                     domain));
      return;
   end

   begin
      vmm_rw_access rw = new;

      rw.data_id     = data_id;
      rw.scenario_id = scenario_id;
      rw.stream_id   = stream_id;

      rw.kind   = vmm_rw::READ;
      rw.addr   = addr;
      rw.n_bits = n_bits;
      this.rw_exec[domain].exec_chan.put(rw);
      rw.notify.wait_for(vmm_data::ENDED);

      data = rw.data;
      status = rw.status;
   end

   `vmm_trace(this.log, $psprintf("Read 'h%h from 'h%h via domain \"%s\"...",
                                  data, addr, domain));

endtask: read


task vmm_ral_access::burst_write(output vmm_rw::status_e              status,
                                 input  bit [`VMM_RAL_ADDR_WIDTH-1:0] start,
                                 input  bit [`VMM_RAL_ADDR_WIDTH-1:0] incr,
                                 input  bit [`VMM_RAL_ADDR_WIDTH-1:0] max,
                                 input  bit [`VMM_RAL_DATA_WIDTH-1:0] data[],
                                 input  vmm_data                      user = null,
                                 input  int                           n_bits = `VMM_RAL_DATA_WIDTH,
                                 input  string                        domain = "",
                                 input  int                           data_id = -1,
                                 input  int                           scenario_id = -1,
                                 input  int                           stream_id = -1);
   status = vmm_rw::ERROR;
   
   if (!this.rw_exec.exists(domain)) begin
      `vmm_error(this.log, $psprintf("No transactor available to physically access domain \"%s\".",
                                     domain));
      return;
   end

   begin
      vmm_rw_burst rw = new;

      rw.data_id     = data_id;
      rw.scenario_id = scenario_id;
      rw.stream_id   = stream_id;

      rw.kind      = vmm_rw::WRITE;
      rw.addr      = start;
      rw.incr_addr = incr;
      rw.max_addr  = max;
      rw.n_beats   = data.size();
      rw.n_bits    = n_bits;
      rw.user_data = user;

      rw.data = new [rw.n_beats];
      foreach (data[i]) rw.data[i] = data[i];

      this.rw_exec[domain].exec_chan.put(rw);
      rw.notify.wait_for(vmm_data::ENDED);

      status = rw.status;
   end

   `vmm_trace(this.log, $psprintf("Burst-wrote %0d data from ['h%h+'h%h %%'h%h] via domain \"%s\"...",
                                  data.size(), start, incr, max, domain));

endtask: burst_write


task vmm_ral_access::burst_read(output vmm_rw::status_e              status,
                                input  bit [`VMM_RAL_ADDR_WIDTH-1:0] start,
                                input  bit [`VMM_RAL_ADDR_WIDTH-1:0] incr,
                                input  bit [`VMM_RAL_ADDR_WIDTH-1:0] max,
                                input  int                           n_beats,
                                output bit [`VMM_RAL_DATA_WIDTH-1:0] data[],
                                input  vmm_data                      user = null,
                                input  int                           n_bits = `VMM_RAL_DATA_WIDTH,
                                input  string                        domain = "",
                                input  int                           data_id = -1,
                                input  int                           scenario_id = -1,
                                input  int                           stream_id = -1);
   status = vmm_rw::ERROR;
   
   if (!this.rw_exec.exists(domain)) begin
      `vmm_error(this.log, $psprintf("No transactor available to physically access domain \"%s\".",
                                     domain));
      return;
   end

   begin
      vmm_rw_burst rw = new;

      rw.data_id     = data_id;
      rw.scenario_id = scenario_id;
      rw.stream_id   = stream_id;

      rw.kind      = vmm_rw::READ;
      rw.addr      = start;
      rw.incr_addr = incr;
      rw.max_addr  = max;
      rw.n_beats   = n_beats;
      rw.n_bits    = n_bits;
      rw.user_data = user;

      this.rw_exec[domain].exec_chan.put(rw);
      rw.notify.wait_for(vmm_data::ENDED);

      data = new [rw.data.size()];
      foreach (data[i]) data[i] = rw.data[i];
      status = rw.status;
   end

   `vmm_trace(this.log, $psprintf("Burst-read %0d data from ['h%h+'h%h %%'h%h] via domain \"%s\"...",
                                  data.size(), start, incr, max, domain));

endtask: burst_read


function bit vmm_ral_access::set_by_name(string                        name,
                                         bit [`VMM_RAL_DATA_WIDTH-1:0] value);
   vmm_ral_reg rg;

   set_by_name = 0;
   rg = this.model.get_reg_by_name(name);
   if (rg == null) return 0;

   rg.set(value);
   set_by_name = 1;
endfunction: set_by_name
	

function bit vmm_ral_access::get_by_name(input string                         name,
                                         output bit [`VMM_RAL_DATA_WIDTH-1:0] value);
   vmm_ral_reg rg;

   get_by_name = 0;
   rg = this.model.get_reg_by_name(name);
   if (rg == null) return 0;

   value = rg.get();
   get_by_name = 1;
endfunction: get_by_name
	

task vmm_ral_access::write_by_name(output vmm_rw::status_e              status,
                                   input  string                        name,
                                   input  bit [`VMM_RAL_DATA_WIDTH-1:0] data,
                                   input  vmm_ral::path_e               path = vmm_ral::DEFAULT,
                                   input  string                        domain = "",
                                   input  int                           data_id = -1,
                                   input  int                           scenario_id = -1,
                                   input  int                           stream_id = -1);
   vmm_ral_reg rg;

   status = vmm_rw::ERROR;
   rg = this.model.get_reg_by_name(name);
   if (rg == null) return;

   rg.write(status, data, path, domain, data_id, scenario_id, stream_id);
endtask: write_by_name


task vmm_ral_access::read_by_name(output vmm_rw::status_e              status,
                                  input  string                        name,
                                  output bit [`VMM_RAL_DATA_WIDTH-1:0] data,
                                  input  vmm_ral::path_e               path = vmm_ral::DEFAULT,
                                  input  string                        domain = "",
                                  input  int                           data_id = -1,
                                  input  int                           scenario_id = -1,
                                  input  int                           stream_id = -1);
   vmm_ral_reg rg;

   status = vmm_rw::ERROR;
   rg = this.model.get_reg_by_name(name);
   if (rg == null) return;

   rg.read(status, data, path, domain, data_id, scenario_id, stream_id);
endtask: read_by_name


task vmm_ral_access::write_mem_by_name(output vmm_rw::status_e              status,
                                       input  string                        name,
                                       input  bit [`VMM_RAL_ADDR_WIDTH-1:0] offset,
                                       input  bit [`VMM_RAL_DATA_WIDTH-1:0] data,
                                       input  vmm_ral::path_e               path = vmm_ral::DEFAULT,
                                       input  string                        domain = "",
                                       input  int                           data_id = -1,
                                       input  int                           scenario_id = -1,
                                       input  int                           stream_id =-1);
   vmm_ral_mem mem;

   status = vmm_rw::ERROR;
   mem = this.model.get_mem_by_name(name);
   if (mem == null) return;

   mem.write(status, offset, data, path, domain, data_id, scenario_id, stream_id);
endtask: write_mem_by_name


task vmm_ral_access::read_mem_by_name(output vmm_rw::status_e              status,
                                      input  string                        name,
                                      input  bit [`VMM_RAL_ADDR_WIDTH-1:0] offset,
                                      output bit [`VMM_RAL_DATA_WIDTH-1:0] data,
                                      input  vmm_ral::path_e               path = vmm_ral::DEFAULT,
                                      input  string                        domain = "",
                                      input  int                           data_id = -1,
                                      input  int                           scenario_id = -1,
                                      input  int                           stream_id = -1);
   vmm_ral_mem mem;

   status = vmm_rw::ERROR;
   mem = this.model.get_mem_by_name(name);
   if (mem == null) return;

   mem.read(status, offset, data, path, domain, data_id, scenario_id, stream_id);
endtask: read_mem_by_name


//
// Identify the sequence of addresses that must be accessed physically
// to access the specified number of bytes at the specified address
// within the specified block or system. Returns the number of bytes
// of valid data in each access.
//
// Returns a list of address in little endian order, with the granularity
// of the top-level system
//
// A register is specified as a base address with mem_indx == 0.
// A location within a memory is specified as an index from a base address.
//
function int vmm_ral_access::Xget_physical_addressesX(bit [`VMM_RAL_ADDR_WIDTH-1:0]     base_addr,
                                                      bit [`VMM_RAL_ADDR_WIDTH-1:0]     mem_offset,
                                                      int unsigned                      n_bytes,
                                                      vmm_ral_block_or_sys              in_block,
                                                      string                            domain,
                                                      ref bit [`VMM_RAL_ADDR_WIDTH-1:0] addr[]);
   int bus_width = in_block.get_n_bytes(domain);
   bit [`VMM_RAL_ADDR_WIDTH-1:0] local_addr[];
   vmm_ral_block_or_sys          parent = in_block.get_parent();

   addr = new [0];
   
   if (n_bytes <= 0) begin
      `vmm_fatal(this.log, $psprintf("Cannot access %0d bytes. Must be greater than 0",
                                     n_bytes));
      return 0;
   end

   // First, identify the addresses within the block/system
   if (n_bytes <= bus_width) begin
      local_addr = new [1];
      local_addr[0] = base_addr + mem_offset;
   end else begin
      int n;

      n = ((n_bytes-1) / bus_width) + 1;
      local_addr = new [n];
      
      base_addr = base_addr + mem_offset * n;

      case (in_block.get_endian(domain))
         vmm_ral::LITTLE_ENDIAN: begin
            foreach (local_addr[i]) begin
               local_addr[i] = base_addr + i;
            end
         end
         vmm_ral::BIG_ENDIAN: begin
            foreach (local_addr[i]) begin
               n--;
               local_addr[i] = base_addr + n;
            end
         end
         vmm_ral::LITTLE_FIFO: begin
            foreach (local_addr[i]) begin
               local_addr[i] = base_addr;
            end
         end
         vmm_ral::BIG_FIFO: begin
            foreach (local_addr[i]) begin
               local_addr[i] = base_addr;
            end
         end
         default: begin
            `vmm_error(this.log, $psprintf("Block has no specified endianness. Cannot access %0d bytes register via its %0d byte \"%s\" interface",
                                           n_bytes, in_block.get_n_bytes(domain), domain));
         end
      endcase
   end


   // Then translate these addresses in the parent's space
   if (parent == null) begin
      // This is the top-most system/block!
      addr = new [local_addr.size()] (local_addr);
   end else begin
      bit [`VMM_RAL_ADDR_WIDTH-1:0] sys_addr[];
      bit [`VMM_RAL_ADDR_WIDTH-1:0] base_addr;
      string                        up_domain;
      int w, k;

      up_domain = in_block.get_parent_domain(domain);

      // Scale the consecutive local address in the system's granularity
      if (bus_width < parent.get_n_bytes(up_domain)) k = 1;
      else k = ((bus_width-1) / parent.get_n_bytes(up_domain)) + 1;

      base_addr = in_block.get_base_addr(domain);
      foreach (local_addr[i]) begin
         int n = addr.size();
         
         w = this.Xget_physical_addressesX(base_addr + local_addr[i] * k, 0,
                                           bus_width, parent, up_domain,
                                           sys_addr);

         addr = new [n + sys_addr.size()] (addr);
         foreach (sys_addr[j]) begin
            addr[n+j] = sys_addr[j];
         end
      end
      // The width of each access is the minimum of this block or the system's width
      if (w < bus_width) bus_width = w;
   end

   Xget_physical_addressesX = bus_width;
endfunction: Xget_physical_addressesX
