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



function xvc_action::new(string name,
                         vmm_log log);
   super.new(log);

   this.name = name;
endfunction: new


function string xvc_action::get_name();
   get_name = this.name;
endfunction: get_name


function xvc_action xvc_action::parse(string argv[]);
   string msg = "Virtual xvc_action::parse() not implemented in derivative";

   if (this.notify.log == null) begin
     $display(msg);
     $finish;
   end
   else `vmm_fatal(this.notify.log, msg);
   parse = null;
endfunction: parse


task xvc_action::execute(vmm_channel exec_chan,
                         xvc_xactor  xvc);
   string msg = "Virtual xvc_action::execute() not implemented in derivative";
   if (this.notify.log == null) begin
     $display(msg);
     $finish;
   end
   else `vmm_fatal(this.notify.log, msg);
endtask: execute


function string xvc_action::psdisplay(string prefix = "");
   $sformat(psdisplay, "%0sXVC Action %0s #%0d.%0d.%0d", prefix, name,
            this.stream_id, this.scenario_id, this.data_id);
endfunction: psdisplay


function bit xvc_action::is_valid(bit silent = 1,
                             int kind = -1);
  is_valid = 1;
endfunction: is_valid


function vmm_data xvc_action::allocate();
   string msg = "Virtual xvc_action::allocate() not implemented in derivative";

   if (this.notify.log == null) begin
     $display(msg);
     $finish;
   end
   else `vmm_fatal(this.notify.log, msg);
   allocate = null;
endfunction: allocate


function vmm_data xvc_action::copy(vmm_data to = null);
   string msg = "Virtual vmm_data::copy() not implemented in derivative";

   if (this.notify.log == null) begin
     $display(msg);
     $finish;
   end
   else`vmm_fatal(this.notify.log, msg);
   copy = to;
endfunction: copy


function void xvc_action::copy_data(vmm_data to);
   xvc_action cpy;

   if (to == null) begin
      string msg = "xvc_action::copy_data() called with non xvc_action instance";

      if (this.notify.log == null) begin
         $display(msg);
         $finish;
      end
      else`vmm_fatal(this.notify.log, msg);
      return;
   end

   if (!$cast(cpy, to)) begin
      string msg = "xvc_action::copy_data() called with null reference";

      if (this.notify.log == null) begin
         $display(msg);
         $finish;
      end
      else`vmm_fatal(this.notify.log, msg);
      return;
   end

   super.copy_data(to);
   cpy.name      = this.name;
   cpy.callbacks = this.callbacks;
endfunction: copy_data


function bit xvc_action::compare(input  vmm_data to,
                                 output string   diff,
                                 input  int      kind = -1);
   string msg = "Virtual xvc_action::compare() not implemented in derivative";
   if (this.notify.log == null) begin
     $display(msg);
     $finish;
   end
   else`vmm_fatal(this.notify.log, msg);
   compare = 0;
endfunction : compare


function int unsigned xvc_action::byte_size(int kind = -1);
   byte_size = this.name.len() + 1;
endfunction : byte_size
   

function int unsigned xvc_action::max_byte_size(int kind = -1);
   max_byte_size = this.name.len() + 1;
endfunction : max_byte_size
   

function int unsigned xvc_action::byte_pack(ref logic [7:0]    bytes[],
                                            input int unsigned offset = 0,
                                            input int          kind = -1);
   int i;

   byte_pack = this.byte_size(kind);
   if (bytes.size() < offset + byte_pack) begin
      bytes = new [offset + byte_pack] (bytes);
   end
   for (i = 0; i < this.name.len(); i++) begin
      bytes[offset + i] = this.name.getc(i);
   end
   bytes[offset + i] = 8'h00;
endfunction : byte_pack


function int unsigned xvc_action::byte_unpack(const ref logic [7:0] bytes[],
                                              input int unsigned    offset = 0,
                                              input int             len = -1,
                                              input int             kind = -1);
   string space = "                                                                                                                       ";
   byte_unpack = 0;
   if (offset >= bytes.size()) return 0;
   if (len < 0) len = bytes.size() - offset;

   this.name = space.substr(0,len);
   while (len > 0 && bytes[byte_unpack + offset] != 8'h00) begin
      byte c = bytes[byte_unpack + offset];
      this.name.putc(byte_unpack, c);
      byte_unpack++;
      len--;
   end
   if (byte_unpack > 0) begin
      // Truncate name to remove trailing " "s
      this.name = this.name.substr(0, byte_unpack-1);
   end
   // Include the terminating 8'h00 in unpack count
   if (len > 0) byte_unpack++;
endfunction : byte_unpack
