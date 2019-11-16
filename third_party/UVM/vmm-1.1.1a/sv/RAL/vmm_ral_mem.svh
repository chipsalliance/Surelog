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


class vmm_ral_mem_burst;
   rand int unsigned                 n_beats;
   rand bit [`VMM_RW_ADDR_WIDTH-1:0] start_offset;
   rand bit [`VMM_RW_ADDR_WIDTH-1:0] incr_offset;
   rand bit [`VMM_RW_ADDR_WIDTH-1:0] max_offset;
        vmm_data                     user_data;
endclass


class vmm_ral_mem_callbacks extends vmm_ral_callbacks;

   virtual task pre_write(vmm_ral_mem                       mem,
                          ref bit [`VMM_RAL_ADDR_WIDTH-1:0] offset,
                          ref bit [`VMM_RAL_DATA_WIDTH-1:0] wdat,
                          ref vmm_ral::path_e               path,
                          ref string                        domain);
   endtask: pre_write

   virtual task post_write(vmm_ral_mem                   mem,
                           bit [`VMM_RAL_ADDR_WIDTH-1:0] offset,
                           bit [`VMM_RAL_DATA_WIDTH-1:0] wdat,
                           vmm_ral::path_e               path,
                           string                        domain,
                           ref vmm_rw::status_e          status);
   endtask: post_write

   virtual task pre_read(vmm_ral_mem                       mem,
                         ref bit [`VMM_RAL_ADDR_WIDTH-1:0] offset,
                         ref vmm_ral::path_e               path,
                         ref string                        domain);
   endtask: pre_read

   virtual task post_read(input vmm_ral_mem                   mem,
                          input bit [`VMM_RAL_ADDR_WIDTH-1:0] offset,
                          ref   bit [`VMM_RAL_DATA_WIDTH-1:0] rdat,
                          input vmm_ral::path_e               path,
                          input string                        domain,
                          ref   vmm_rw::status_e              status);
   endtask: post_read

   virtual task pre_burst(vmm_ral_mem                       mem,
                          vmm_rw::kind_e                    kind,
                          vmm_ral_mem_burst                 burst,
                          ref bit [`VMM_RAL_DATA_WIDTH-1:0] wdat[],
                          ref vmm_ral::path_e               path,
                          ref string                        domain);
   endtask: pre_burst

   virtual task post_burst(input vmm_ral_mem                   mem,
                           input vmm_rw::kind_e                kind,
                           input vmm_ral_mem_burst             burst,
                           ref   bit [`VMM_RAL_DATA_WIDTH-1:0] data[],
                           input vmm_ral::path_e               path,
                           input string                        domain,
                           ref   vmm_rw::status_e              status);
   endtask: post_burst
endclass: vmm_ral_mem_callbacks


virtual class vmm_ral_mem_frontdoor;
   static vmm_log log = new("vmm_ral_mem_frontdoor", "class");
   
   extern virtual task write(output vmm_rw::status_e              status,
                             input  bit [`VMM_RAL_ADDR_WIDTH-1:0] offset,
                             input  bit [`VMM_RAL_DATA_WIDTH-1:0] data,
                             input  int                           data_id = -1,
                             input  int                           scenario_id = -1,
                             input  int                           stream_id = -1);
   extern virtual task read(output vmm_rw::status_e              status,
                            input  bit [`VMM_RAL_ADDR_WIDTH-1:0] offset,
                            output bit [`VMM_RAL_DATA_WIDTH-1:0] data,
                            input  int                           data_id = -1,
                            input  int                           scenario_id = -1,
                            input  int                           stream_id = -1);
   extern virtual task burst_write(output vmm_rw::status_e              status,
                                   input  vmm_ral_mem_burst             burst,
                                   input  bit [`VMM_RAL_DATA_WIDTH-1:0] data[],
                                   input  int                           data_id = -1,
                                   input  int                           scenario_id = -1,
                                   input  int                           stream_id = -1);
   extern virtual task burst_read(output vmm_rw::status_e              status,
                                  input  vmm_ral_mem_burst             burst,
                                  output bit [`VMM_RAL_DATA_WIDTH-1:0] data[],
                                  input  int                           data_id = -1,
                                  input  int                           scenario_id = -1,
                                  input  int                           stream_id = -1);
endclass: vmm_ral_mem_frontdoor


class vmm_ral_mem;
   static vmm_log log = new("RAL", "memory");

   vmm_mam mam;

   typedef enum {UNKNOWNS, ZEROES, ONES, ADDRESS, VALUE, INCR, DECR} init_e;

   local string name;
   local bit locked;

   local vmm_ral::access_e access;
   local longint unsigned size;

   local vmm_ral_block parent;

   local logic [`VMM_RAL_ADDR_WIDTH-1:0] offset_in_block[];
   local string                          domains[];
   local vmm_ral::access_e               rights[];

   local int unsigned  n_bits;
   local string        constraint_block_names[];

   local vmm_ral_access ral_access;
   local vmm_ral_mem_frontdoor frontdoor[];
   local vmm_ral_mem_backdoor backdoor;

   local vmm_ral_mem_callbacks callbacks[$];

   local string attributes[string];

   local bit is_powered_down;

   local int has_cover;
   local int cover_on;

   static vmm_ral_mem all_mems[*]; // Keeps track of all memories in the RAL Model
   static local int unsigned mem_id_factory = 0;
   local int unsigned mem_id = 0;

   /*local*/ vmm_ral_vreg XvregsX[$]; //Virtual registers implemented here

   extern function new(vmm_ral_block                 parent,
                       string                        name,
                       vmm_ral::access_e             access,
                       longint unsigned              size,
                       int unsigned                  n_bits,
                       bit [`VMM_RAL_ADDR_WIDTH-1:0] base_addr,
                       string                        domain   = "",
                       int                           cover_on = vmm_ral::NO_COVERAGE,
                       bit [1:0]                     rights   = 2'b11,
                       bit                           unmapped = 0,
                       int                           has_cover = vmm_ral::NO_COVERAGE);

   /*local*/ extern function void Xlock_modelX();
   /*local*/ extern function void add_domain(bit [`VMM_RAL_ADDR_WIDTH-1:0] base_addr,
                                             string                        domain,
                                             bit [1:0]                     rights,
                                             bit                           unmapped = 0);

   /*local*/ extern function void Xregister_ral_accessX(vmm_ral_access access);

   extern virtual function string get_name();
   extern virtual function string get_fullname();
   extern virtual function int get_n_domains();
   extern virtual function void get_domains(ref string domains[]);
   extern virtual function vmm_ral::access_e get_access(string domain = "");
   extern /*local*/ function vmm_ral_access Xget_ral_accessX();
   extern virtual function vmm_ral::access_e get_rights(string domain = "");
   extern virtual function void get_virtual_fields(ref vmm_ral_vfield fields[]);
   extern virtual function vmm_ral_vfield get_virtual_field_by_name(string name);
   extern virtual function void get_virtual_registers(ref vmm_ral_vreg regs[]);
   extern virtual function vmm_ral_vreg get_vreg_by_name(string name);
   extern virtual function vmm_ral_vreg get_vreg_by_offset(bit [63:0] offset,
                                                           string domain = "");
   extern virtual function vmm_ral_block get_block();
   extern virtual function bit [`VMM_RAL_ADDR_WIDTH-1:0] get_offset_in_block(bit [`VMM_RAL_ADDR_WIDTH-1:0] mem_addr = 0,
                                                                             string                        domain   = "");
   extern virtual function bit [`VMM_RAL_ADDR_WIDTH-1:0] get_address_in_system(bit [`VMM_RAL_ADDR_WIDTH-1:0] mem_addr = 0,
                                                            string                                           domain   = "");
   extern virtual function longint unsigned get_size();
   extern virtual function int unsigned get_n_bits();
   extern         function int unsigned get_n_bytes();

   extern virtual function void display(string prefix = "",
                                        string domain = "");
   extern virtual function string psdisplay(string prefix = "",
                                            string domain = "");

   extern virtual function void set_attribute(string name,
                                              string value);
   extern virtual function string get_attribute(string name,
                                                bit inherited = 1);
   extern virtual function void get_all_attributes(ref string names[],
                                                   input bit inherited = 1);

   extern virtual function void ral_power_down();
   extern virtual function void ral_power_up();

   extern virtual function bit can_cover(int models);
   extern virtual function int set_cover(int is_on);
   extern virtual function bit is_cover_on(int is_on = vmm_ral::ALL_COVERAGE);

   extern virtual task init(output bit                           is_ok,
                            input  init_e                        pattern,
                            input  bit [`VMM_RAL_DATA_WIDTH-1:0] data);

   extern virtual task write(output vmm_rw::status_e              status,
                             input  bit [`VMM_RAL_ADDR_WIDTH-1:0] mem_addr,
                             input  bit [`VMM_RAL_DATA_WIDTH-1:0] value,
                             input  vmm_ral::path_e               path   = vmm_ral::DEFAULT,
                             input  string                        domain = "",
                             input  int                           data_id = -1,
                             input  int                           scenario_id = -1,
                             input  int                           stream_id = -1);

   extern virtual task read(output vmm_rw::status_e              status,
                            input  bit [`VMM_RAL_ADDR_WIDTH-1:0] mem_addr,
                            output bit [`VMM_RAL_DATA_WIDTH-1:0] value,
                            input  vmm_ral::path_e               path   = vmm_ral::DEFAULT,
                            input  string                        domain = "",
                            input  int                           data_id = -1,
                            input  int                           scenario_id = -1,
                            input  int                           stream_id = -1);

   extern local function bit validate_burst(vmm_ral_mem_burst burst);

   extern virtual task burst_write(output vmm_rw::status_e              status,
                                   input  vmm_ral_mem_burst             burst,
                                   input  bit [`VMM_RAL_DATA_WIDTH-1:0] value[],
                                   input  vmm_ral::path_e               path   = vmm_ral::DEFAULT,
                                   input  string                        domain = "",
                                   input  int                           data_id = -1,
                                   input  int                           scenario_id = -1,
                                   input  int                           stream_id = -1);

   extern virtual task burst_read(output vmm_rw::status_e              status,
                                  input  vmm_ral_mem_burst             burst,
                                  output bit [`VMM_RAL_DATA_WIDTH-1:0] value[],
                                  input  vmm_ral::path_e               path   = vmm_ral::DEFAULT,
                                  input  string                        domain = "",
                                  input  int                           data_id = -1,
                                  input  int                           scenario_id = -1,
                                  input  int                           stream_id = -1);

   extern virtual task poke(output vmm_rw::status_e              status,
                            input  bit [`VMM_RAL_ADDR_WIDTH-1:0] mem_addr,
                            input  bit [`VMM_RAL_DATA_WIDTH-1:0] value,
                            input  int                           data_id = -1,
                            input  int                           scenario_id = -1,
                            input  int                           stream_id = -1);

   extern virtual task peek(output vmm_rw::status_e              status,
                            input  bit [`VMM_RAL_ADDR_WIDTH-1:0] mem_addr,
                            output bit [`VMM_RAL_DATA_WIDTH-1:0] value,
                            input  int                           data_id = -1,
                            input  int                           scenario_id = -1,
                            input  int                           stream_id = -1);

   extern virtual task readmemh(string filename);
   extern virtual task writememh(string filename);

   extern function void set_frontdoor(vmm_ral_mem_frontdoor ftdr,
                                      string                domain = "");
   extern function vmm_ral_mem_frontdoor get_frontdoor(string domain = "");
   extern function void set_backdoor(vmm_ral_mem_backdoor bkdr);
   extern function vmm_ral_mem_backdoor get_backdoor();

   extern function void prepend_callback(vmm_ral_mem_callbacks cb);
   extern function void append_callback(vmm_ral_mem_callbacks cb);
   extern function void unregister_callback(vmm_ral_mem_callbacks cb);

   extern local function int get_domain_index(string domain);

   extern function int unsigned get_mem_ID();
endclass: vmm_ral_mem
