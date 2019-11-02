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


function vmm_data::new(vmm_log log = null
                       `VMM_DATA_BASE_NEW_EXTERN_ARGS);
`ifdef VMM_DATA_BASE_NEW_CALL
   super.new(`VMM_DATA_BASE_NEW_CALL);
`endif

   if (log == null) log = this.get_vmm_log();
   this.notify = new(log);
   `VMM_OBJECT_SET_PARENT(this.notify, this)

   void'(this.notify.configure(EXECUTE, vmm_notify::ON_OFF));
   void'(this.notify.configure(STARTED, vmm_notify::ON_OFF));
   void'(this.notify.configure(ENDED,   vmm_notify::ON_OFF));
   this.notify.indicate(EXECUTE);
endfunction: new


function vmm_log vmm_data::set_log(vmm_log log);
   set_log = this.notify.log;
   this.notify.log = log;
endfunction: set_log


function string vmm_data::this_class_name();
   return "vmm_data";
endfunction: this_class_name


function vmm_log vmm_data::get_vmm_log();
   if (this.notify == null) return null;
   return this.notify.log;
endfunction


function void vmm_data::display(string prefix="");
   $display(this.psdisplay(prefix));
endfunction: display


function string vmm_data::psdisplay(string prefix="");
   $sformat(psdisplay, "%0sclass %s (%0d.%0d.%0d)", prefix,
            this.this_class_name(), this.stream_id, this.scenario_id, this.data_id);
endfunction: psdisplay


function bit vmm_data::is_valid(bit silent = 1,
                                int kind = -1);
  is_valid = 1;
endfunction: is_valid


function vmm_data vmm_data::allocate();
   string msg = "Virtual vmm_data::allocate() not implemented in derivative";
   vmm_log log = this.get_vmm_log();
   if (log == null) begin
     $display(msg);
     $finish;
   end
   else `vmm_fatal(log, msg);
   allocate = null;
endfunction: allocate


function vmm_data vmm_data::copy(vmm_data to = null);
   string msg = "Virtual vmm_data::copy() not implemented in derivative";

   if (to == null) begin
      vmm_log log = this.get_vmm_log();
      if (log == null) begin
         $display(msg);
         $finish;
      end
      else`vmm_fatal(log, msg);
   end

   this.copy_data(to);
   return to;
endfunction: copy


function void vmm_data::copy_data(vmm_data to);
   if (to == null) begin
      string msg = "vmm_data::copy_data() called with null reference";
      vmm_log log = this.get_vmm_log();

      if (log == null) begin
         $display(msg);
         $finish;
      end
      else`vmm_fatal(log, msg);
      return;
   end
   else begin
`ifdef VMM_DATA_BASE_COPY_DATA_CALL
      `VMM_DATA_BASE_COPY_DATA_CALL ;
`endif
      to.stream_id   = this.stream_id;
      to.scenario_id = this.scenario_id;
      to.data_id     = this.data_id;
   end
endfunction: copy_data

   


function bit vmm_data::compare(       vmm_data to,
                               output string   diff,
                               input  int      kind = -1);
   return 1;
endfunction : compare


function int unsigned vmm_data::__vmm_byte_size(int kind = -1);
   return 0;
endfunction : __vmm_byte_size


function int unsigned vmm_data::byte_size(int kind = -1);
   return 0;
endfunction : byte_size


function int unsigned vmm_data::max_byte_size(int kind = -1);
   max_byte_size = 0;
endfunction : max_byte_size


function int unsigned vmm_data::byte_pack(ref   logic [7:0]  bytes[],
                                          input int unsigned offset = 0,
                                          input int          kind = -1);
   return 0;
endfunction : byte_pack




function int unsigned vmm_data::byte_unpack(const ref logic [7:0] bytes[],
                                            input int unsigned    offset = 0,
                                            input int             len = -1,
                                            input int             kind = -1);
   return 0;
endfunction : byte_unpack


function string vmm_data::do_psdisplay(string prefix = "");
   this.__vmm_done_user = 0;
   return "";
endfunction: do_psdisplay


function bit vmm_data::do_is_valid(bit silent = 1,
                                   int kind = -1);
  this.__vmm_done_user = 0;
  return 0;
endfunction: do_is_valid


function vmm_data vmm_data::do_allocate();
   this.__vmm_done_user = 0;
   return null;
endfunction: do_allocate


function vmm_data vmm_data::do_copy(vmm_data to = null);
   this.__vmm_done_user = 0;
   return null;
endfunction: do_copy

   
function bit vmm_data::do_compare(       vmm_data to,
                                  output string   diff,
                                  input  int      kind = -1);
   this.__vmm_done_user = 0;
   return 0;
endfunction : do_compare


function int unsigned vmm_data::do_byte_size(int kind = -1);
   this.__vmm_done_user = 0;
   return 0;
endfunction : do_byte_size


function int unsigned vmm_data::do_max_byte_size(int kind = -1);
   this.__vmm_done_user = 0;
   return 0;
endfunction : do_max_byte_size


function int unsigned vmm_data::do_byte_pack(ref   logic [7:0]  bytes[],
                                             input int unsigned offset = 0,
                                             input int          kind = -1);
   this.__vmm_done_user = 0;
   return 0;
endfunction : do_byte_pack


function int unsigned vmm_data::do_byte_unpack(const ref logic [7:0] bytes[],
                                               input int unsigned    offset =0,
                                               input int             len = -1,
                                               input int             kind = -1);
   this.__vmm_done_user = 0;
   return 0;
endfunction : do_byte_unpack



function bit vmm_data::load(int file);
   int len, i;
   logic [7:0] bytes[];
   bit escaped = 0;

   load = 0;

   // Expect one record for the object, with the following format:
   // [<blanks>]<n><SPACE><n bytes (potentially inclusing \n)>\n
   if ($fscanf(file, " %d", len) != 1) begin
      string msg = "Invalid input record in vmm_data::load()";
      vmm_log log = this.get_vmm_log();
      if (log == null) begin
         $display(msg);
         $finish;
      end
      else`vmm_fatal(log, msg);
      return 0;
   end

   // Skip the <SPACE>
   begin
      bit [7:0] c;
      c = $fgetc(file);
   end

   // Read the next 'len' characters and unpack
   bytes = new [len];
   i = 0;
   while (i < len) begin
      int c = $fgetc(file);
      if (c < 0) begin
         string msg = "Truncated input record in vmm_data::load()";
         vmm_log log = this.get_vmm_log();
         if (log == null) begin
            $display(msg);
            $finish;
         end
         else`vmm_fatal(log, msg);
         return 0;
      end
      bytes[i] = c;
      // Some characters have been escaped
      if (bytes[i] == 8'h2E) begin
         escaped = 1;
         continue;
      end
      if (escaped) begin
         bit [7:0] c = bytes[i];
         c[7] = ~c[7];
         bytes[i] = c;
         escaped = 0;
      end
      i++;
   end
   i = this.byte_unpack(bytes);
   if (i != len) begin
      string msg = `vmm_sformatf("Unable to fully unpack input record in vmm_data::load(): %0d bytes were unpacked instead of the full %0d.", len, i);
      vmm_log log = this.get_vmm_log();
      if (log == null) begin
         $display(msg);
         $finish;
      end
      else`vmm_fatal(log, msg);
      return 0;
   end

   // Skip the final \n
   begin
      bit [7:0] c;
      c = $fgetc(file);
      if (c != "\n") begin
         string msg = "Corrupted record in file: extra characters present";
         vmm_log log = this.get_vmm_log();
         if (log == null) begin
            $display(msg);
            $finish;
         end
         else`vmm_fatal(log, msg);
      end
   end

   load = 1;
endfunction: load
   

function void vmm_data::save(int file);
   logic [7:0] bytes[];
   int   i;

   // Produce the format expected by vmm_data::load()
   void'(this.byte_pack(bytes));
   $fwrite(file, "%0d ", bytes.size());
   for (i = 0; i < bytes.size(); i++) begin
      bit [7:0] a_byte = bytes[i]; // Make sure there are no X's
      // Some characters need to be escaped
      case (a_byte)
      8'h00,
      8'hFF,
      8'h2E: begin
         bit [7:0] c = a_byte;
         c[7] = ~c[7];
         $fwrite(file, ".%c", c);
      end

      default: $fwrite(file, "%c", a_byte);
      endcase
   end
   $fwrite(file, "\n");
endfunction: save



`ifdef VCS
function int vmm_data::vmt_hook(vmm_xactor xactor = null,
     			        vmm_data   obj = null);
endfunction: vmt_hook

`endif
