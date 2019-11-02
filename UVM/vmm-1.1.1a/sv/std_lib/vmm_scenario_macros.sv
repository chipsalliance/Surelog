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


`define vmm_scenario_member_begin(_class) \
 \
   `vmm_data_member_begin(_class)

`define vmm_scenario_member_scalar(_name, _do) \
  \
   `vmm_data_member_scalar(_name, _do)

`define vmm_scenario_member_scalar_array(_name, _do) \
 \
  `vmm_data_member_scalar_array(_name, _do)

`define vmm_scenario_member_scalar_da(_name, _do) \
 \
  `vmm_data_member_scalar_da(_name, _do)

`define vmm_scenario_member_scalar_aa_scalar(_name, _do) \
 \
  `vmm_data_member_scalar_aa_scalar(_name, _do)

`define vmm_scenario_member_scalar_aa_string(_name, _do) \
 \
  `vmm_data_member_scalar_aa_string(_name, _do)

`define vmm_scenario_member_string(_name, _do) \
  \
  `vmm_data_member_string(_name, _do)

`define vmm_scenario_member_string_array(_name, _do) \
 \
  `vmm_data_member_string_array(_name, _do)

`define vmm_scenario_member_string_da(_name, _do) \
 \
  `vmm_data_member_string_da(_name, _do)

`define vmm_scenario_member_string_aa_scalar(_name, _do) \
 \
  `vmm_data_member_string_aa_scalar(_name, _do)

`define vmm_scenario_member_string_aa_string(_name, _do) \
 \
  `vmm_data_member_string_aa_string(_name, _do)

`define vmm_scenario_member_enum(_name, _do) \
\
  `vmm_data_member_enum(_name, _do)

`define vmm_scenario_member_enum_array(_name, _do) \
\
  `vmm_data_member_enum_array(_name, _do)

`define vmm_scenario_member_enum_da(_name, _do) \
\
  `vmm_data_member_enum_da(_name, _do)

`define vmm_scenario_member_enum_aa_scalar(_name, _do) \
 \
  `vmm_data_member_enum_aa_scalar(_name, _do)

`define vmm_scenario_member_enum_aa_string(_name, _do) \
 \
  `vmm_data_member_enum_aa_string(_name, _do)

`define vmm_scenario_member_handle(_name, _do) \
  \
  `vmm_data_member_handle(_name, _do)

`define vmm_scenario_member_handle_array(_name, _do) \
 \
  `vmm_data_member_handle_array(_name, _do)

`define vmm_scenario_member_handle_da(_name, _do) \
 \
  `vmm_data_member_handle_da(_name, _do)

`define vmm_scenario_member_handle_aa_scalar(_name, _do) \
 \
  `vmm_data_member_handle_aa_scalar(_name, _do)

`define vmm_scenario_member_handle_aa_string(_name, _do) \
 \
  `vmm_data_member_handle_aa_string(_name, _do)

`define vmm_scenario_member_vmm_data(_name, _do, _how) \
  \
  `vmm_data_member_vmm_data(_name, _do, _how)

`define vmm_scenario_member_vmm_data_array(_name, _do, _how) \
 \
  `vmm_data_member_vmm_data_array(_name, _do, _how)

`define vmm_scenario_member_vmm_data_da(_name, _do, _how) \
 \
  `vmm_data_member_vmm_data_da(_name, _do, _how)

`define vmm_scenario_member_vmm_data_aa_scalar(_name, _do, _how) \
 \
  `vmm_data_member_vmm_data_aa_scalar(_name, _do, _how)

`define vmm_scenario_member_vmm_data_aa_string(_name, _do, _how) \
 \
  `vmm_data_member_vmm_data_aa_string(_name, _do, _how)

`define vmm_scenario_member_vmm_scenario(_name, _do) \
  \
      case (do_what & _do) \
        DO_PRINT: begin \
          if ( _name == null ) begin \
             $sformat(this.__vmm_image, `"%s\n%s%s: (null)`", this.__vmm_image, \
                      this.__vmm_prefix, `"_name`"); \
          end \
          else begin \
	     string _prefix = this.__vmm_prefix; \
             $sformat(this.__vmm_image, `"%s\n%s`", this.__vmm_image, this._name.psdisplay({this.__vmm_prefix, `"_name: `"})); \
	     this.__vmm_prefix = _prefix; \
          end \
        end \
        DO_COPY: begin \
           if (_name == null) begin \
              __vmm_rhs._name = this._name; \
           end \
           else begin \
	      $cast(__vmm_rhs._name, this._name.copy()); \
           end \
        end \
        DO_COMPARE: begin \
           if (_name == null || __vmm_rhs._name == null) begin \
              if (this._name != __vmm_rhs._name) begin \
              	 $sformat(this.__vmm_image, `"this._name !== to._name`"); \
       	         this.__vmm_status = 0; \
              	 return; \
              end \
           end \
           else begin \
	      string diff; \
              if (!this._name.compare(__vmm_rhs._name, diff)) begin \
                 $sformat(this.__vmm_image, `"this._name !== to._name: %s `", diff); \
                 this.__vmm_status = 0; \
                 return; \
	      end \
           end \
        end \
      endcase


`define vmm_scenario_member_user_defined(_name) \
 \
  `vmm_data_member_user_defined(_name)


`define vmm_scenario_new(_class) \
 \
   `define vmm_scenario_``_class``_new 1 \
 \
   static `VMM_LOG log = new(`"_class`", `"class`"); \


`define vmm_scenario_member_end(_class) \
   endfunction \
 \
   `ifndef vmm_scenario_``_class``_new \
      static `VMM_LOG log = new(`"_class`", `"class`"); \
 \
      function new(`VMM_SCENARIO parent = null); \
         super.new(parent); \
      endfunction \
   `endif \
 \
  `vmm_data_methods(_class)
