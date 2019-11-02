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


`define vmm_xactor_member_begin(_class) \
 \
   function void do_all(vmm_xactor::do_what_e do_what, \
                        vmm_xactor::reset_e   rst_typ = SOFT_RST); \
      super.do_all(do_what, rst_typ);


`define vmm_xactor_member_scalar(_name, _do) \
  \
      case (do_what & _do) \
        DO_PRINT: begin \
           $sformat(this.__vmm_image, `"%s\n%s%s: %0d`", this.__vmm_image, \
                    this.__vmm_prefix, `"_name`", this._name); \
        end \
      endcase


`define vmm_xactor_member_scalar_array(_name, _do) \
  \
      case (do_what & _do) \
        DO_PRINT: begin \
           `foreach (this._name,i) begin \
              $sformat(this.__vmm_image, `"%s\n%s%s[%0d]: %0d`", \
                       this.__vmm_image, this.__vmm_prefix, \
                       `"_name`", i, this._name[i]); \
           end \
        end \
      endcase


`define vmm_xactor_member_scalar_aa_scalar(_name, _do) \
  \
   `vmm_xactor_member_scalar_array(_name, _do)
   

`define vmm_xactor_member_scalar_aa_string(_name, _do) \
  \
      case (do_what & _do) \
        DO_PRINT: begin \
           `foreach_aa (this._name,string,i) begin \
              $sformat(this.__vmm_image, `"%s\n%s%s[%s]: %0d`", \
                       this.__vmm_image, this.__vmm_prefix, \
                       `"_name`", i, this._name[i]); \
           end \
           `foreach_aa_end (this._name,i) \
        end \
      endcase


`define vmm_xactor_member_enum(_name, _do) \
  \
      case (do_what & _do) \
        DO_PRINT: begin \
           $sformat(this.__vmm_image, `"%s\n%s%s: %0s`", this.__vmm_image, \
                    this.__vmm_prefix, `"_name`", this._name.name()); \
        end \
      endcase


`define vmm_xactor_member_enum_array(_name, _do) \
  \
      case (do_what & _do) \
        DO_PRINT: begin \
           `foreach (this._name,i) begin \
              $sformat(this.__vmm_image, `"%s\n%s%s[%0d]: %0s`", \
                       this.__vmm_image, this.__vmm_prefix, \
                       `"_name`", i, this._name[i].name()); \
           end \
        end \
      endcase


`define vmm_xactor_member_enum_aa_scalar(_name, _do) \
  \
   `define vmm_xactor_member_enum_array(_name, _do)


`define vmm_xactor_member_enum_aa_string(_name, _do) \
  \
      case (do_what & _do) \
        DO_PRINT: begin \
           `foreach_aa (this._name,string,i) begin \
              $sformat(this.__vmm_image, `"%s\n%s%s[%s]: %s`", \
                       this.__vmm_image, this.__vmm_prefix, \
                       `"_name`", i, this._name[i].name()); \
           end \
           `foreach_aa_end (this._name,i) \
        end \
      endcase


`define vmm_xactor_member_string(_name, _do) \
  \
      case (do_what & _do) \
        DO_PRINT: begin \
           $sformat(this.__vmm_image, `"%s\n%s%s: %s`", this.__vmm_image, \
                    this.__vmm_prefix, `"_name`", this._name); \
        end \
      endcase


`define vmm_xactor_member_string_array(_name, _do) \
  \
      case (do_what & _do) \
        DO_PRINT: begin \
           `foreach (this._name,i) begin \
              $sformat(this.__vmm_image, `"%s\n%s%s[%0d]: %s`", \
                       this.__vmm_image, this.__vmm_prefix, \
                       `"_name`", i, this._name[i]); \
           end \
        end \
      endcase


`define vmm_xactor_member_string_aa_scalar(_name, _do) \
  \
   `vmm_xactor_member_string_array(_name, _do)


`define vmm_xactor_member_string_aa_string(_name, _do) \
  \
      case (do_what & _do) \
        DO_PRINT: begin \
           `foreach_aa (this._name,string,i) begin \
              $sformat(this.__vmm_image, `"%s\n%s%s[%s]: %s`", \
                       this.__vmm_image, this.__vmm_prefix, \
                       `"_name`", i, this._name[i]); \
           end \
           `foreach_aa_end (this._name,i) \
        end \
      endcase


`define vmm_xactor_member_vmm_data(_name, _do) \
  \
      if(_name != null) begin \
      case (do_what & _do) \
        DO_PRINT: begin \
           $sformat(this.__vmm_image, `"%s\n%s`", this.__vmm_image, \
                    this._name.psdisplay({this.__vmm_prefix, `"_name: `"})); \
        end \
      endcase \
      end


`define vmm_xactor_member_vmm_data_array(_name, _do) \
  \
      case (do_what & _do) \
        DO_PRINT: begin \
           `foreach (this._name,i) begin \
              $sformat(this.__vmm_image, `"%s\n%s`", this.__vmm_image, \
                       this._name[i].psdisplay(`vmm_sformatf("%s%s[%0d]: ", \
                                                             this.__vmm_prefix, \
                                                             `"_name`", i))); \
           end \
        end \
      endcase


`define vmm_xactor_member_vmm_data_aa_scalar(_name, _do) \
  \
   `vmm_xactor_member_vmm_data_array(_name, _do)


`define vmm_xactor_member_vmm_data_aa_string(_name, _do) \
  \
      case (do_what & _do) \
        DO_PRINT: begin \
           `foreach_aa (this._name,string,i) begin \
              $sformat(this.__vmm_image, `"%s\n%s`", this.__vmm_image, \
                       this._name[i].psdisplay(`vmm_sformatf("%s%s[%s]: ", \
                                                             this.__vmm_prefix, \
                                                             `"_name`", i))); \
           end \
           `foreach_aa_end (this._name,i) \
        end \
      endcase


`define vmm_xactor_member_channel(_name, _do) \
  \
      if(_name != null) begin \
      case (do_what & _do) \
        DO_PRINT: begin \
           $sformat(this.__vmm_image, `"%s\n%s`", this.__vmm_image, \
                    this._name.psdisplay({this.__vmm_prefix, `"_name: `"})); \
        end \
        DO_RESET: begin \
           this._name.flush(); \
        end \
        DO_KILL: begin \
           this._name.kill(); \
        end \
      endcase \
      end


`define vmm_xactor_member_channel_array(_name, _do) \
  \
      case (do_what & _do) \
        DO_PRINT: begin \
           `foreach (this._name,i) begin \
              $sformat(this.__vmm_image, `"%s\n%s`", this.__vmm_image, \
                       this._name[i].psdisplay(`vmm_sformatf("%s%s[%0d]: ", \
                                                             this.__vmm_prefix, \
                                                             `"_name`", i))); \
           end \
        end \
        DO_RESET: begin \
           `foreach (this._name,i) begin \
              this._name[i].flush(); \
           end \
        end \
        DO_KILL: begin \
           `foreach (this._name,i) begin \
              this._name[i].kill(); \
           end \
        end \
      endcase


`define vmm_xactor_member_channel_aa_scalar(_name, _do) \
  \
   `vmm_xactor_member_channel_array(_name, _do)


`define vmm_xactor_member_channel_aa_string(_name, _do) \
  \
      case (do_what & _do) \
        DO_PRINT: begin \
           `foreach_aa (this._name,string,i) begin \
              $sformat(this.__vmm_image, `"%s\n%s`", this.__vmm_image, \
                       this._name[i].psdisplay(`vmm_sformatf("%s%s[%s]: ", \
                                                             this.__vmm_prefix, \
                                                             `"_name`", i))); \
           end \
           `foreach_aa_end (this._name,i) \
        end \
        DO_RESET: begin \
           `foreach_aa (this._name,string,i) begin \
              this._name[i].flush(); \
           end \
           `foreach_aa_end (this._name,i) \
        end \
        DO_KILL: begin \
           `foreach_aa (this._name,string,i) begin \
              this._name[i].kill(); \
           end \
           `foreach_aa_end (this._name,i) \
        end \
      endcase


`define vmm_xactor_member_xactor(_name, _do) \
  \
      if(_name != null) begin \
      case (do_what & _do) \
        DO_PRINT: begin \
           string _prefix = this.__vmm_prefix; \
           $sformat(this.__vmm_image, `"%s\n%s`", this.__vmm_image, \
                    this._name.psdisplay({this.__vmm_prefix, `"_name: `"})); \
           this.__vmm_prefix = _prefix; \
        end \
        DO_START: begin \
           this._name.start_xactor(); \
        end \
        DO_STOP: begin \
           this._name.stop_xactor(); \
        end \
        DO_RESET: begin \
           this._name.reset_xactor(rst_typ); \
        end \
        DO_KILL: begin \
           this._name.kill(); \
        end \
      endcase \
      end


`define vmm_xactor_member_xactor_array(_name, _do) \
  \
      case (do_what & _do) \
        DO_PRINT: begin \
           string _prefix = this.__vmm_prefix; \
           `foreach (this._name,i) begin \
              $sformat(this.__vmm_image, `"%s\n%s`", this.__vmm_image, \
                       this._name[i].psdisplay(`vmm_sformatf("%s%s[%0d]: ", \
                                                             _prefix, \
                                                             `"_name`", i))); \
           end \
           this.__vmm_prefix = _prefix; \
        end \
        DO_START: begin \
           `foreach (this._name,i) begin \
              this._name[i].start_xactor(); \
           end \
        end \
        DO_STOP: begin \
           `foreach (this._name,i) begin \
              this._name[i].stop_xactor(); \
           end \
        end \
        DO_RESET: begin \
           `foreach (this._name,i) begin \
              this._name[i].reset_xactor(rst_typ); \
           end \
        end \
        DO_KILL: begin \
           `foreach (this._name,i) begin \
              this._name[i].kill(); \
           end \
        end \
      endcase


`define vmm_xactor_member_xactor_aa_scalar(_name, _do) \
  \
   `vmm_xactor_member_xactor_array(_name, _do)


`define vmm_xactor_member_xactor_aa_string(_name, _do) \
  \
      case (do_what & _do) \
        DO_PRINT: begin \
           string _prefix = this.__vmm_prefix; \
           `foreach_aa (this._name,string,i) begin \
              $sformat(this.__vmm_image, `"%s\n%s`", this.__vmm_image, \
                       this._name[i].psdisplay(`vmm_sformatf("%s%s[%s]: ", \
                                                             _prefix, \
                                                             `"_name`", i))); \
           end \
           `foreach_aa_end (this._name,i) \
           this.__vmm_prefix = _prefix; \
        end \
        DO_START: begin \
           `foreach_aa (this._name,string,i) begin \
              this._name[i].start_xactor(); \
           end \
           `foreach_aa_end (this._name,i) \
        end \
        DO_STOP: begin \
           `foreach_aa (this._name,string,i) begin \
              this._name[i].stop_xactor(); \
           end \
           `foreach_aa_end (this._name,i) \
        end \
        DO_RESET: begin \
           `foreach_aa (this._name,string,i) begin \
              this._name[i].reset_xactor(rst_typ); \
           end \
           `foreach_aa_end (this._name,i) \
        end \
        DO_KILL: begin \
           `foreach_aa (this._name,string,i) begin \
              this._name[i].kill(); \
           end \
           `foreach_aa_end (this._name,i) \
        end \
      endcase


`define vmm_xactor_member_user_defined(_name) \
 \
      void'(this.do_``_name(do_what, rst_typ));


`define vmm_xactor_member_end(_class) \
   endfunction \
 \
   virtual function string psdisplay(string prefix = `"`"); \
      this.__vmm_done_user = 1; \
      psdisplay = this.do_psdisplay(prefix); \
      if (this.__vmm_done_user) return psdisplay; \
 \
      this.__vmm_image = super.psdisplay(prefix); \
      this.__vmm_prefix = prefix; \
      if (`vmm_str_match(prefix, ": $")) begin \
         this.__vmm_prefix = {`vmm_str_prematch(prefix), "."}; \
      end \
      this.do_all(DO_PRINT); \
      return this.__vmm_image; \
   endfunction \
 \
   virtual function void start_xactor(); \
      super.start_xactor(); \
      this.__vmm_done_user = 1; \
      this.do_start_xactor(); \
      if (this.__vmm_done_user) return; \
 \
      this.do_all(DO_START); \
   endfunction \
 \
   virtual function void stop_xactor(); \
      super.stop_xactor(); \
      this.__vmm_done_user = 1; \
      this.do_stop_xactor(); \
      if (this.__vmm_done_user) return; \
 \
      this.do_all(DO_STOP); \
   endfunction \
 \
   virtual function void reset_xactor(vmm_xactor::reset_e rst_typ = SOFT_RST); \
      super.reset_xactor(rst_typ); \
      this.__vmm_done_user = 1; \
      this.do_reset_xactor(rst_typ); \
      if (this.__vmm_done_user) return; \
 \
      this.do_all(DO_RESET, rst_typ); \
   endfunction \
 \
   virtual function void kill(); \
      super.kill(); \
      this.__vmm_done_user = 1; \
      this.do_kill_xactor(); \
      if (this.__vmm_done_user) return; \
 \
      this.do_all(DO_KILL); \
   endfunction
