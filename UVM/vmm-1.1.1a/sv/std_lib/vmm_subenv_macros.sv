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


`define vmm_subenv_member_begin(_class) \
 \
   function void do_all(vmm_subenv::do_what_e do_what, \
                        vmm_env::restart_e restart = vmm_env::FIRM); \
      super.do_all(do_what, restart);


`define vmm_subenv_member_scalar(_name, _do) \
  `define vmm_xactor_member_scalar(_name, _do)

`define vmm_subenv_member_scalar_array(_name, _do) \
  `vmm_xactor_member_scalar_array(_name, _do)

`define vmm_subenv_member_scalar_aa_scalar(_name, _do) \
  `vmm_xactor_member_scalar_aa_scalar(_name, _do)

`define vmm_subenv_member_scalar_aa_string(_name, _do) \
  `vmm_xactor_member_scalar_aa_string(_name, _do)

`define vmm_subenv_member_enum(_name, _do) \
  `vmm_xactor_member_enum(_name, _do)

`define vmm_subenv_member_enum_array(_name, _do) \
  `vmm_xactor_member_enum_array(_name, _do)

`define vmm_subenv_member_enum_aa_scalar(_name, _do) \
  `vmm_xactor_member_enum_aa_scalar(_name, _do)

`define vmm_subenv_member_enum_aa_string(_name, _do) \
  `vmm_xactor_member_enum_aa_string(_name, _do)

`define vmm_subenv_member_string(_name, _do) \
  `vmm_xactor_member_string(_name, _do)

`define vmm_subenv_member_string_array(_name, _do) \
  `vmm_xactor_member_string_array(_name, _do)

`define vmm_subenv_member_string_aa_scalar(_name, _do) \
  `vmm_xactor_member_string_aa_scalar(_name, _do)

`define vmm_subenv_member_string_aa_string(_name, _do) \
  `vmm_xactor_member_string_aa_string(_name, _do)

`define vmm_subenv_member_vmm_data(_name, _do) \
  `vmm_xactor_member_vmm_data(_name, _do)

`define vmm_subenv_member_vmm_data_array(_name, _do) \
  `vmm_xactor_member_vmm_data_array(_name, _do)

`define vmm_subenv_member_vmm_data_aa_scalar(_name, _do) \
  `vmm_xactor_member_vmm_data_aa_scalar(_name, _do)

`define vmm_subenv_member_vmm_data_aa_string(_name, _do) \
  `vmm_xactor_member_vmm_data_aa_string(_name, _do)


`define vmm_subenv_member_channel(_name, _do) \
  \
      if(_name != null) begin \
      case (do_what & _do) \
        DO_PRINT: begin \
           $sformat(this.__vmm_image, `"%s\n%s`", this.__vmm_image, \
                    this._name.psdisplay({this.__vmm_prefix, `"_name: `"})); \
        end \
        DO_RESET: begin \
           case (restart) \
           vmm_env::FIRM: this._name.flush(); \
           vmm_env::HARD: this._name.kill(); \
           endcase \
        end \
        DO_VOTE: begin \
           this.end_test.register_channel(this._name); \
        end \
      endcase \
      end


`define vmm_subenv_member_channel_array(_name, _do) \
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
           case (restart) \
           vmm_env::FIRM: `foreach (this._name,i) begin \
              this._name[i].flush(); \
           end \
           vmm_env::HARD: `foreach (this._name,i) begin \
              this._name[i].kill(); \
           end \
           endcase \
        end \
        DO_VOTE: begin \
           `foreach (this._name,i) begin \
              this.end_test.register_channel(this._name[i]); \
           end \
        end \
      endcase


`define vmm_subenv_member_channel_aa_scalar(_name, _do) \
  \
   `vmm_subenv_member_channel_array(_name, _do)


`define vmm_subenv_member_channel_aa_string(_name, _do) \
  \
      case (do_what & _do) \
        DO_PRINT: begin \
           `foreach (this._name,i) begin \
              $sformat(this.__vmm_image, `"%s\n%s`", this.__vmm_image, \
                       this._name[i].psdisplay(`vmm_sformatf("%s%s[%s]: ", \
                                                             this.__vmm_prefix, \
                                                             `"_name`", i))); \
           end \
        end \
        DO_RESET: begin \
           case (restart) \
           vmm_env::FIRM: `foreach (this._name,i) begin \
              this._name[i].flush(); \
           end \
           vmm_env::HARD: `foreach (this._name,i) begin \
              this._name[i].kill(); \
           end \
           endcase \
        end \
        DO_VOTE: begin \
           `foreach (this._name,i) begin \
              this.end_test.register_channel(this._name[i]); \
           end \
        end \
      endcase


`define vmm_subenv_member_xactor(_name, _do) \
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
           case (restart) \
           vmm_env::FIRM: this._name.reset_xactor(vmm_xactor::SOFT_RST); \
           vmm_env::HARD: this._name.kill(); \
           endcase \
        end \
        DO_VOTE: begin \
           this.end_test.register_xactor(this._name); \
        end \
      endcase \
      end


`define vmm_subenv_member_xactor_array(_name, _do) \
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
           case (restart) \
           vmm_env::FIRM: `foreach (this._name,i) begin \
              this._name[i].reset_xactor(); \
           end \
           vmm_env::HARD: `foreach (this._name,i) begin \
              this._name[i].kill(); \
           end \
           endcase \
        end \
        DO_VOTE: begin \
           `foreach (this._name,i) begin \
              this.end_test.register_xactor(this._name[i]); \
           end \
        end \
      endcase


`define vmm_subenv_member_xactor_aa_scalar(_name, _do) \
  `vmm_subenv_member_xactor_array(_name, _do)


`define vmm_subenv_member_xactor_aa_string(_name, _do) \
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
           `foreach_aa_end(this._name,i) \
           this.__vmm_prefix = _prefix; \
        end \
        DO_START: begin \
           `foreach_aa (this._name,string,i) begin \
              this._name[i].start_xactor(); \
           end \
           `foreach_aa_end(this._name,i) \
        end \
        DO_STOP: begin \
           `foreach_aa (this._name,string,i) begin \
              this._name[i].stop_xactor(); \
           end \
           `foreach_aa_end(this._name,i) \
        end \
        DO_RESET: begin \
           case (restart) \
           vmm_env::FIRM: `foreach_aa (this._name,string,i) begin \
              this._name[i].reset_xactor(); \
           end \
           `foreach_aa_end(this._name,i) \
           vmm_env::HARD: `foreach_aa (this._name,string,i) begin \
              this._name[i].kill(); \
           end \
           `foreach_aa_end(this._name,i) \
           endcase \
        end \
        DO_VOTE: begin \
           `foreach_aa (this._name,string,i) begin \
              this.end_test.register_xactor(this._name[i]); \
           end \
           `foreach_aa_end(this._name,i) \
        end \
      endcase


`define vmm_subenv_member_subenv(_name, _do) \
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
           this.__vmm_forks++; \
           fork \
              begin \
                 this._name.start(); \
                 this.__vmm_forks--; \
              end \
           join_none \
        end \
        DO_STOP: begin \
           this.__vmm_forks++; \
           fork \
              begin \
                 this._name.stop(); \
                 this.__vmm_forks--; \
              end \
           join_none \
        end \
        DO_RESET: begin \
           this.__vmm_forks++; \
           fork \
              begin \
                 this._name.reset(restart); \
                 this.__vmm_forks--; \
              end \
           join_none \
        end \
      endcase \
      end


`define vmm_subenv_member_subenv_array(_name, _do) \
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
           this.__vmm_forks++; \
           `foreach (this._name,i) begin \
              automatic int j = i; \
              fork \
                 begin \
                    this._name[j].start(); \
                    this.__vmm_forks--; \
                 end \
              join_none \
           end \
        end \
        DO_STOP: begin \
           this.__vmm_forks++; \
           `foreach (this._name,i) begin \
              automatic int j = i; \
              fork \
                 begin \
                    this._name[j].stop(); \
                    this.__vmm_forks--; \
                 end \
              join_none \
           end \
        end \
        DO_RESET: begin \
           this.__vmm_forks++; \
           `foreach (this._name,i) begin \
              automatic int j = i; \
              fork \
                 begin \
                    this._name[j].reset(restart); \
                    this.__vmm_forks--; \
                 end \
              join_none \
           end \
        end \
      endcase


`define vmm_subenv_member_subenv_aa_scalar(_name, _do) \
  `vmm_subenv_member_subenv_array(_name, _do)


`define vmm_subenv_member_subenv_aa_string(_name, _do) \
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
           `foreach_aa_end(this._name,i) \
           this.__vmm_prefix = _prefix; \
        end \
        DO_START: begin \
           this.__vmm_forks++; \
           `foreach_aa (this._name,string,i) begin \
              automatic string j = i; \
              fork \
                 begin \
                    this._name[j].start(); \
                    this.__vmm_forks--; \
                 end \
              join_none \
           end \
           `foreach_aa_end(this._name,i) \
        end \
        DO_STOP: begin \
           this.__vmm_forks++; \
           `foreach_aa (this._name,string,i) begin \
              automatic string j = i; \
              fork \
                 begin \
                    this._name[j].stop(); \
                    this.__vmm_forks--; \
                 end \
              join_none \
           end \
           `foreach_aa_end(this._name,i) \
        end \
        DO_RESET: begin \
           this.__vmm_forks++; \
           `foreach_aa (this._name,string,i) begin \
              automatic int j = i; \
              fork \
                 begin \
                    this._name[j].reset(restart); \
                    this.__vmm_forks--; \
                 end \
              join_none \
           end \
           `foreach_aa_end(this._name,i) \
        end \
      endcase


`define vmm_subenv_member_user_defined(_name) \
 \
      this.__vmm_restart = restart; \
      void'(this.do_``_name(do_what));


`define vmm_subenv_member_end(_class) \
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
   virtual task start(); \
      super.start(); \
      this.__vmm_done_user = 1; \
      this.do_vote(); \
      if (!this.__vmm_done_user) begin \
         this.do_all(DO_VOTE); \
      end \
 \
      this.__vmm_done_user = 1; \
      this.do_start(); \
      if (this.__vmm_done_user) return; \
 \
      this.__vmm_forks = 0; \
      this.do_all(DO_START); \
      wait (this.__vmm_forks == 0); \
   endtask \
 \
   virtual task stop(); \
      super.stop(); \
      this.__vmm_done_user = 1; \
      this.do_stop(); \
      if (this.__vmm_done_user) return; \
 \
      this.__vmm_forks = 0; \
      this.do_all(DO_STOP); \
      wait (this.__vmm_forks == 0); \
   endtask \
 \
   virtual task reset(vmm_env::restart_e kind = vmm_env::FIRM); \
      super.stop(); \
      this.__vmm_done_user = 1; \
      this.do_reset(kind); \
      if (this.__vmm_done_user) return; \
 \
      this.__vmm_forks = 0; \
      this.do_all(DO_RESET, kind); \
      wait (this.__vmm_forks == 0); \
   endtask \
