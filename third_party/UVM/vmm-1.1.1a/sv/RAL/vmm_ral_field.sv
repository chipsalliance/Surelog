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


typedef class vmm_ral_field;
class vmm_ral_field_callbacks extends vmm_ral_callbacks;

   virtual task pre_write(vmm_ral_field                     field,
                          ref bit [`VMM_RAL_DATA_WIDTH-1:0] wdat,
                          ref vmm_ral::path_e               path,
                          ref string                        domain);
   endtask: pre_write

   virtual task post_write(vmm_ral_field                 field,
                           bit [`VMM_RAL_DATA_WIDTH-1:0] wdat,
                           vmm_ral::path_e               path,
                           string                        domain,
                           ref vmm_rw::status_e          status);
   endtask: post_write

   virtual task pre_read(vmm_ral_field         field,
                         ref vmm_ral::path_e   path,
                         ref string            domain);
   endtask: pre_read

   virtual task post_read(vmm_ral_field                     field,
                          ref bit [`VMM_RAL_DATA_WIDTH-1:0] rdat,
                          vmm_ral::path_e                   path,
                          string                            domain,
                          ref vmm_rw::status_e              status);
   endtask: post_read
endclass: vmm_ral_field_callbacks


class vmm_ral_field;
   static vmm_log log = new("RAL", "field");

   local string name;
   local vmm_ral::access_e access;
   local vmm_ral_reg parent;
   local int unsigned lsb;
   local int unsigned size;
   local bit [`VMM_RAL_DATA_WIDTH-1:0] mirrored; // What we think is in the HW
   local bit [`VMM_RAL_DATA_WIDTH-1:0] desired;  // Mirrored after set()
   rand  bit [`VMM_RAL_DATA_WIDTH-1:0] value;    // Mirrored after randomize()
   local bit [`VMM_RAL_DATA_WIDTH-1:0] reset_value;
   local logic [`VMM_RAL_DATA_WIDTH-1:0] soft_reset_value;
   local bit written;

   vmm_ral_field_callbacks XcbsX[$];

   constraint vmm_ral_field_valid {
      if (`VMM_RAL_DATA_WIDTH > size) {
         value < (`VMM_RAL_DATA_WIDTH'h1 << size);
      }
   }

   extern function new(vmm_ral_reg                   parent,
                       string                        name,
                       int unsigned                  size,
                       vmm_ral::access_e             access,
                       bit [`VMM_RAL_DATA_WIDTH-1:0] reset,
                       logic [`VMM_RAL_DATA_WIDTH-1:0] soft_reset,
                       int unsigned                  lsb_pos,
                       bit                           is_rand = 0,
                       bit                           cover_on = vmm_ral::NO_COVERAGE); 
                                                             // Ignoring cover_on - It is not yet used/supported 
                                                             // in the field level.

   extern virtual function string get_name();
   extern virtual function string get_fullname();
   extern virtual function vmm_ral_reg get_register();
   extern virtual function int unsigned get_lsb_pos_in_register();
   extern virtual function int unsigned get_n_bits();
   extern virtual function vmm_ral::access_e get_access(string domain = "");
   extern virtual function vmm_ral::access_e set_access(vmm_ral::access_e mode);

   extern virtual function void display(string prefix = "");
   extern virtual function string psdisplay(string prefix = "");


   /*local*/ extern virtual function bit [`VMM_RAL_DATA_WIDTH-1:0] XpredictX(bit [`VMM_RAL_DATA_WIDTH-1:0] cur_val,
                                                                             bit [`VMM_RAL_DATA_WIDTH-1:0] wr_val,
                                                                             string                        domain);

   /*local*/ extern virtual function void XforceX(bit [`VMM_RAL_DATA_WIDTH-1:0] value,
                                                  vmm_ral::path_e               path,
                                                  string                        domain);
   /*local*/ extern virtual function void XwroteX(bit [`VMM_RAL_DATA_WIDTH-1:0] value,
                                                  vmm_ral::path_e               path,
                                                  string                        domain);
   /*local*/ extern virtual function bit[`VMM_RAL_DATA_WIDTH-1:0] XupdX();

   extern virtual function void set(bit[`VMM_RAL_DATA_WIDTH-1:0] value);
   extern virtual function bit predict(bit [`VMM_RAL_DATA_WIDTH-1:0] value);
   extern virtual function bit[`VMM_RAL_DATA_WIDTH-1:0] get();
   extern virtual function void reset(vmm_ral::reset_e kind = vmm_ral::HARD);
   extern virtual function logic [`VMM_RAL_DATA_WIDTH-1:0]
                    get_reset(vmm_ral::reset_e kind = vmm_ral::HARD);
   extern virtual function logic [`VMM_RAL_DATA_WIDTH-1:0]
                    set_reset(logic [`VMM_RAL_DATA_WIDTH-1:0] value,
                              vmm_ral::reset_e                kind = vmm_ral::HARD);
   extern virtual function bit needs_update();

   extern virtual task write(output vmm_rw::status_e              status,
                             input  bit [`VMM_RAL_DATA_WIDTH-1:0] value,
                             input  vmm_ral::path_e               path = vmm_ral::DEFAULT,
                             input  string                        domain = "",
                             input  int                           data_id = -1,
                             input  int                           scenario_id =- 1,
                             input  int                           stream_id = -1);
   extern virtual task read(output vmm_rw::status_e             status,
                            output bit[`VMM_RAL_DATA_WIDTH-1:0] value,
                            input  vmm_ral::path_e              path = vmm_ral::DEFAULT,
                            input  string                       domain = "",
                            input  int                          data_id = -1,
                            input  int                          scenario_id = -1,
                            input  int                          stream_id = -1);
               
   extern virtual task poke(output vmm_rw::status_e              status,
                            input  bit [`VMM_RAL_DATA_WIDTH-1:0] value,
                            input  int                           data_id = -1,
                            input  int                           scenario_id =- 1,
                            input  int                           stream_id = -1);
   extern virtual task peek(output vmm_rw::status_e             status,
                            output bit[`VMM_RAL_DATA_WIDTH-1:0] value,
                            input  int                          data_id = -1,
                            input  int                          scenario_id = -1,
                            input  int                          stream_id = -1);
               
   extern virtual task mirror(output vmm_rw::status_e status,
                              input  vmm_ral::check_e check = vmm_ral::QUIET,
                              input  vmm_ral::path_e  path = vmm_ral::DEFAULT,
                              input  string           domain = "");

   extern function void prepend_callback(vmm_ral_field_callbacks cb);
   extern function void append_callback(vmm_ral_field_callbacks cb);
   extern function void unregister_callback(vmm_ral_field_callbacks cb);

   extern function void pre_randomize();
   extern function void post_randomize();
endclass: vmm_ral_field


function vmm_ral_field::new(vmm_ral_reg                   parent,
                            string                        name,
                            int unsigned                  size,
                            vmm_ral::access_e             access,
                            bit [`VMM_RAL_DATA_WIDTH-1:0] reset,
                            logic [`VMM_RAL_DATA_WIDTH-1:0] soft_reset,
                            int unsigned                  lsb_pos,
                            bit                           is_rand = 0,
                            bit                           cover_on = vmm_ral::NO_COVERAGE);
                                                             // Ignoring cover_on - It is not yet used/supported 
                                                             // in the field level.
   this.parent = parent;
   this.name   = name;

   if (size == 0) begin
      `vmm_error(this.log, $psprintf("Field \"%s\" cannot have 0 bits", name));
      size = 1;
   end
   if (size > `VMM_RAL_DATA_WIDTH) begin
      `vmm_error(this.log, $psprintf("Field \"%s\" cannot have more than %0d bits",
                                     name, `VMM_RAL_DATA_WIDTH));
      size = `VMM_RAL_DATA_WIDTH;
   end
   this.size   = size;

   this.access = access;
   this.reset_value = reset;
   this.soft_reset_value = soft_reset;
   this.lsb    = lsb_pos;
   this.parent.register_field(this);
   if (!is_rand) this.value.rand_mode(0);

   this.written = 0;

endfunction: new


function string vmm_ral_field::get_name();
   get_name = this.name;
endfunction: get_name


function string vmm_ral_field::get_fullname();
   get_fullname = {this.parent.get_fullname(), ".", this.name};
endfunction: get_fullname


function vmm_ral_reg vmm_ral_field::get_register();
   get_register = this.parent;
endfunction: get_register


function int unsigned vmm_ral_field::get_lsb_pos_in_register();
   get_lsb_pos_in_register = this.lsb;
endfunction: get_lsb_pos_in_register


function int unsigned vmm_ral_field::get_n_bits();
   get_n_bits = this.size;
endfunction: get_n_bits


function vmm_ral::access_e vmm_ral_field::get_access(string domain = "");
   get_access = this.access;
   if (parent.get_n_domains() == 1 || domain == "BaCkDoOr") return get_access;

   // Is the register restricted in this domain?
   case (this.parent.get_rights(domain))
     vmm_ral::RW:
       // No restrictions
       return get_access;

     vmm_ral::RO:
       case (get_access)
         vmm_ral::RW,
         vmm_ral::RO,
         vmm_ral::W1,
         vmm_ral::W1C: get_access = vmm_ral::RO;

         vmm_ral::RU,
         vmm_ral::A0,
         vmm_ral::A1: get_access = vmm_ral::RU;

         vmm_ral::WO: begin
            `vmm_error(this.log,
                       $psprintf("WO field \"%s\" restricted to RO in domain \"%s\"",
                                 this.get_name(), domain));
         end

         // No change for the other modes (OTHER, USERx)
       endcase

     vmm_ral::WO:
       case (get_access)
         vmm_ral::RW,
         vmm_ral::WO: get_access = vmm_ral::WO;

         vmm_ral::RO,
         vmm_ral::RU,
         vmm_ral::W1C,
         vmm_ral::A0,
         vmm_ral::A1: begin
            `vmm_error(this.log,
                       $psprintf("%s field \"%s\" restricted to WO in domain \"%s\"",
                                 get_access.name(), this.get_name(), domain));
         end

         // No change for the other modes (W1, OTHER, USERx)
       endcase

     default:
       `vmm_error(this.log,
                  $psprintf("Shared register \"%s\" containing field \"%s\" is not shared in domain \"%s\"",
                            this.parent.get_name(), this.get_name(), domain));
   endcase
endfunction: get_access


function vmm_ral::access_e vmm_ral_field::set_access(vmm_ral::access_e mode);
   set_access = this.access;
   this.access = mode;
endfunction: set_access


function void vmm_ral_field::display(string prefix = "");
   $write("%s\n", this.psdisplay(prefix));
endfunction: display


function string vmm_ral_field::psdisplay(string prefix = "");
   string fmt;
   $sformat(fmt, "%0d'h%%%0dh", this.get_n_bits(),
            (this.get_n_bits()-1)/4 + 1);
   $sformat(psdisplay, {"%s%s[%0d-%0d] = ",fmt,"%s"}, prefix,
            this.get_name(),
            this.get_lsb_pos_in_register() + this.get_n_bits() - 1,
            this.get_lsb_pos_in_register(), this.desired,
            (this.desired != this.mirrored) ? $psprintf({" (Mirror: ",fmt,")"}, this.mirrored) : "");
endfunction: psdisplay



function bit [`VMM_RAL_DATA_WIDTH-1:0] vmm_ral_field::XpredictX(bit [`VMM_RAL_DATA_WIDTH-1:0] cur_val,
                                                                bit [`VMM_RAL_DATA_WIDTH-1:0] wr_val,
                                                                string                        domain);

   case (this.get_access(domain))
     vmm_ral::RW:    return wr_val;
     vmm_ral::RO:    return cur_val;
     vmm_ral::WO:    return wr_val;
     vmm_ral::W1:    return (this.written) ? cur_val : wr_val;
     vmm_ral::RU:    return cur_val;
     vmm_ral::RC:    return cur_val;
     vmm_ral::W1C:   return cur_val & (~wr_val);
     vmm_ral::A0:    return cur_val | wr_val;
     vmm_ral::A1:    return cur_val & wr_val;
     vmm_ral::DC:    return wr_val;
     vmm_ral::OTHER,
     vmm_ral::USER0,
     vmm_ral::USER1,
     vmm_ral::USER2,
     vmm_ral::USER3: return wr_val;
   endcase

   `vmm_fatal(log, "vmm_ral_field::XpredictX(): Internal error");
   return 0;
endfunction: XpredictX


function void vmm_ral_field::XforceX(bit[`VMM_RAL_DATA_WIDTH-1:0] value,
                                     vmm_ral::path_e              path,
                                     string                       domain);
   value &= ('b1 << this.size)-1;

   // If the value was obtained via a front-door access
   // then a RC field will have been cleared
   if (path == vmm_ral::BFM && this.get_access(domain) == vmm_ral::RC) begin
      value = 0;
   end

   // If the value of a WO field was obtained via a front-door access
   // it will always read back as 0 and the value of the field
   // cannot be inferred from it
   if (path == vmm_ral::BFM && this.get_access(domain) == vmm_ral::WO) return;

   this.mirrored = value;
   this.desired = value;
   this.value   = value;
endfunction: XforceX


function void vmm_ral_field::XwroteX(bit[`VMM_RAL_DATA_WIDTH-1:0] value,
                                     vmm_ral::path_e              path,
                                     string                       domain);
   if (value >> this.size) begin
      `vmm_warning(this.log, $psprintf("Specified value (0x%h) greater than field \"%s\" size (%0d bits)",
                                       value, this.get_name(), this.size));
      value &= ('b1 << this.size)-1;
   end

   if (path == vmm_ral::BFM) begin
      this.mirrored = this.XpredictX(this.mirrored, value, domain);
   end
   else this.mirrored = value;

   this.desired = this.mirrored;
   this.value   = this.mirrored;

   this.written = 1;
endfunction: XwroteX


function bit [`VMM_RAL_DATA_WIDTH-1:0] vmm_ral_field::XupdX();
   // Figure out which value must be written to get the desired value
   // given what we think is the current value in the hardware
   XupdX = 0;

   case (this.access)
      vmm_ral::RW:    XupdX = this.desired;
      vmm_ral::RO:    XupdX = this.desired;
      vmm_ral::WO:    XupdX = this.desired;
      vmm_ral::W1:    XupdX = this.desired;
      vmm_ral::RU:    XupdX = this.desired;
      vmm_ral::RC:    XupdX = this.desired;
      vmm_ral::W1C:   XupdX = ~this.desired;
      vmm_ral::A0:    XupdX = this.desired;
      vmm_ral::A1:    XupdX = this.desired;
      vmm_ral::DC,
      vmm_ral::OTHER,
      vmm_ral::USER0,
      vmm_ral::USER1,
      vmm_ral::USER2,
      vmm_ral::USER3: XupdX = this.desired;
   endcase
endfunction: XupdX


function void vmm_ral_field::set(bit[`VMM_RAL_DATA_WIDTH-1:0] value);
   if (value >> this.size) begin
      `vmm_warning(this.log, $psprintf("Specified value (0x%h) greater than field \"%s\" size (%0d bits)",
                                       value, this.get_name(), this.size));
      value &= ('b1 << this.size)-1;
   end

   case (this.access)
      vmm_ral::RW:    this.desired = value;
      vmm_ral::RO:    this.desired = this.desired;
      vmm_ral::WO:    this.desired = value;
      vmm_ral::W1:    this.desired = (this.written) ? this.desired : value;
      vmm_ral::RU:    this.desired = this.desired;
      vmm_ral::RC:    this.desired = this.desired;
      vmm_ral::W1C:   this.desired &= (~value);
      vmm_ral::A0:    this.desired |= value;
      vmm_ral::A1:    this.desired &= value;
      vmm_ral::DC,
      vmm_ral::OTHER,
      vmm_ral::USER0,
      vmm_ral::USER1,
      vmm_ral::USER2,
      vmm_ral::USER3: this.desired = value;
   endcase
   this.value = this.desired;
endfunction: set

 
function bit vmm_ral_field::predict(bit[`VMM_RAL_DATA_WIDTH-1:0] value);
   if (this.parent.Xis_busyX) begin
      `vmm_warning(this.log, $psprintf("Trying to predict value of field \"%s\" while register \"%s\" is being accessed",
                                       this.get_name(),
                                       this.parent.get_fullname()));
      return 0;
   end
   
   value &= ('b1 << this.size)-1;
   this.mirrored = value;
   this.desired = value;
   this.value   = value;

   return 1;
endfunction: predict


function bit[`VMM_RAL_DATA_WIDTH-1:0] vmm_ral_field::get();
   get = this.desired;
endfunction: get


function void vmm_ral_field::reset(vmm_ral::reset_e kind = vmm_ral::HARD);
   case (kind)
     vmm_ral::HARD: begin
        this.mirrored = reset_value;
        this.desired  = reset_value;
        this.written  = 0;
     end
     vmm_ral::SOFT: begin
        if (soft_reset_value !== 'x) begin
           this.mirrored = soft_reset_value;
           this.desired  = soft_reset_value;
        end
     end
   endcase
   this.value = this.desired;
endfunction: reset


function logic [`VMM_RAL_DATA_WIDTH-1:0]
   vmm_ral_field::get_reset(vmm_ral::reset_e kind = vmm_ral::HARD);

   if (kind == vmm_ral::SOFT) return this.soft_reset_value;

   return this.reset_value;
endfunction: get_reset


function logic [`VMM_RAL_DATA_WIDTH-1:0]
   vmm_ral_field::set_reset(logic [`VMM_RAL_DATA_WIDTH-1:0] value,
                            vmm_ral::reset_e kind = vmm_ral::HARD);
   case (kind)
     vmm_ral::HARD: begin
        set_reset = this.reset_value;
        this.reset_value = value;
     end
     vmm_ral::SOFT: begin
        set_reset = this.soft_reset_value;
        this.soft_reset_value = value;
     end
   endcase
endfunction: set_reset


function bit vmm_ral_field::needs_update();
   needs_update = (this.mirrored != this.desired);
endfunction: needs_update


task vmm_ral_field::write(output vmm_rw::status_e              status,
                          input  bit [`VMM_RAL_DATA_WIDTH-1:0] value,
                          input  vmm_ral::path_e               path = vmm_ral::DEFAULT,
                          input  string                        domain = "",
                          input  int                           data_id = -1,
                          input  int                           scenario_id = -1,
                          input  int                           stream_id = -1);
   bit [`VMM_RAL_DATA_WIDTH-1:0] tmp;
   vmm_ral_field fields[];

   this.parent.XatomicX(1);

   if (value >> this.size) begin
      `vmm_warning(log, $psprintf("vmm_ral_field::write(): Value greater than field \"%s\" size", this.get_name()));
      value &= value & ((1<<this.size)-1);
   end

   tmp = 0;
   // What values are written for the other fields???
   this.parent.get_fields(fields);
   foreach (fields[i]) begin
      if (fields[i] == this) begin
         tmp |= value << this.lsb;
         continue;
      end

      // It depends on what kind of bits they are made of...
      case (fields[i].get_access(domain))
        // These...
        vmm_ral::RW,
        vmm_ral::RO,
        vmm_ral::WO,
        vmm_ral::W1,
        vmm_ral::RU,
        vmm_ral::DC,
        vmm_ral::OTHER,
        vmm_ral::USER0,
        vmm_ral::USER1,
        vmm_ral::USER2,
        vmm_ral::USER3:
          // Use their mirrored value
          tmp |= fields[i].get() << fields[i].get_lsb_pos_in_register();

        // These...
        vmm_ral::RC,
        vmm_ral::W1C,
        vmm_ral::A0:
          // Use all 0's
          tmp |= 0;

        // These...
        vmm_ral::A1:
          // Use all 1's
          tmp |= ((1<<fields[i].get_n_bits())-1) << fields[i].get_lsb_pos_in_register();

        default:
          `vmm_fatal(log, "Internal error: write() does not handle field access mode");
      endcase
   end

   this.parent.XwriteX(status, tmp, path, domain, data_id, scenario_id, stream_id);

   this.parent.XatomicX(0);
endtask: write


task vmm_ral_field::read(output vmm_rw::status_e             status,
                         output bit[`VMM_RAL_DATA_WIDTH-1:0] value,
                         input  vmm_ral::path_e              path = vmm_ral::DEFAULT,
                         input  string                       domain = "",
                         input  int                          data_id = -1,
                         input  int                          scenario_id = -1,
                         input  int                          stream_id = -1);
   bit[`VMM_RAL_DATA_WIDTH-1:0] reg_value;

   this.parent.read(status, reg_value, path, domain, data_id, scenario_id, stream_id);
   value = (reg_value >> lsb) & ((1<<size))-1;
endtask: read
               

task vmm_ral_field::poke(output vmm_rw::status_e              status,
                         input  bit [`VMM_RAL_DATA_WIDTH-1:0] value,
                         input  int                           data_id = -1,
                         input  int                           scenario_id = -1,
                         input  int                           stream_id = -1);
   bit [`VMM_RAL_DATA_WIDTH-1:0] tmp;

   this.parent.XatomicX(1);
   this.parent.Xis_locked_by_fieldX = 1'b1;

   if (value >> this.size) begin
      `vmm_warning(log, $psprintf("vmm_ral_field::poke(): Value greater than field \"%s\" size", this.get_name()));
      value &= value & ((1<<this.size)-1);
   end

   tmp = 0;
   // What is the current values of the other fields???
   this.parent.peek(status, tmp, data_id, scenario_id, stream_id);
   if (status != vmm_rw::IS_OK) begin
      `vmm_error(log, $psprintf("vmm_ral_field::poke(): Peeking register \"%s\" returned status %s", this.parent.get_fullname(), status.name()));
      this.parent.XatomicX(0);
      this.parent.Xis_locked_by_fieldX = 1'b0;
      return;
   end

   // Force the value for this field then poke the resulting value
   tmp &= ~(((1<<this.size)-1) << this.lsb);
   tmp |= value << this.lsb;
   this.parent.poke(status, tmp, data_id, scenario_id, stream_id);

   this.parent.XatomicX(0);
   this.parent.Xis_locked_by_fieldX = 1'b0;
endtask: poke


task vmm_ral_field::peek(output vmm_rw::status_e             status,
                         output bit[`VMM_RAL_DATA_WIDTH-1:0] value,
                         input  int                          data_id = -1,
                         input  int                          scenario_id = -1,
                         input  int                          stream_id = -1);
   bit[`VMM_RAL_DATA_WIDTH-1:0] reg_value;

   this.parent.peek(status, reg_value, data_id, scenario_id, stream_id);
   value = (reg_value >> lsb) & ((1<<size))-1;
endtask: peek
               

task vmm_ral_field::mirror(output vmm_rw::status_e status,
                           input  vmm_ral::check_e check = vmm_ral::QUIET,
                           input  vmm_ral::path_e  path = vmm_ral::DEFAULT,
                           string                  domain = "");
   this.parent.mirror(status, check, path, domain);
endtask: mirror


function void vmm_ral_field::prepend_callback(vmm_ral_field_callbacks cb);
   `foreach (this.XcbsX,i) begin
      if (this.XcbsX[i] == cb) begin
         `vmm_warning(this.log, $psprintf("Callback has already been registered with field \"%s\"", this.get_name()));
         return;
      end
   end
   
   // Prepend new callback
   this.XcbsX.push_front(cb);
endfunction: prepend_callback


function void vmm_ral_field::append_callback(vmm_ral_field_callbacks cb);
   `foreach (this.XcbsX,i) begin
      if (this.XcbsX[i] == cb) begin
         `vmm_warning(this.log, $psprintf("Callback has already been registered with field \"%s\"", this.get_name()));
         return;
      end
   end
   
   // Append new callback
   this.XcbsX.push_back(cb);
endfunction: append_callback


function void vmm_ral_field::unregister_callback(vmm_ral_field_callbacks cb);
   `foreach (this.XcbsX,i) begin
      if (this.XcbsX[i] == cb) begin
         int j = i;
         // Unregister it
         this.XcbsX.delete(j);
         return;
      end
   end

   `vmm_warning(this.log, $psprintf("Callback was not registered with field \"%s\"", this.get_name()));
endfunction: unregister_callback


function void vmm_ral_field::pre_randomize();
   // Update the only publicly known property with the current
   // desired value so it can be used as a state variable should
   // the rand_mode of the field be turned off.
   this.value = this.desired;
endfunction: pre_randomize


function void vmm_ral_field::post_randomize();
   this.desired = this.value;
endfunction: post_randomize
