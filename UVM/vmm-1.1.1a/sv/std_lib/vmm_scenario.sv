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




function vmm_scenario::new(`VMM_SCENARIO parent = null
                           `VMM_SCENARIO_BASE_NEW_ARGS);
   super.new(this.get_vmm_log() `VMM_SCENARIO_BASE_NEW_CALL);
   this.set_parent_scenario(parent);
endfunction: new


function string vmm_scenario::this_class_name();
   return "vmm_scenario";
endfunction: this_class_name


function vmm_log vmm_scenario::get_vmm_log();
   return null;
endfunction


function string vmm_scenario::psdisplay(string prefix = "");
   int i;

   $sformat(psdisplay,
            "%sScenario \"%s\": kind=%0d, length=%0d (max=%0d), repeated=%0d",
            prefix, this.scenario_name(this.scenario_kind),
            this.scenario_kind, this.length, this.max_length,
            this.repeated);
endfunction: psdisplay


function int unsigned vmm_scenario::define_scenario(string name,
                                                    int unsigned max_len = 0);
   define_scenario = this.next_scenario_kind++;
   this.scenario_names[define_scenario] = name;

   if (max_len > this.max_length) this.max_length = max_len;
endfunction: define_scenario


function void vmm_scenario::redefine_scenario(int unsigned scenario_kind,
                                              string       name,
                                              int unsigned max_len = 0);
   this.scenario_names[scenario_kind] = name;
    if (max_len > this.max_length) this.max_length = max_len;
endfunction: redefine_scenario


function string vmm_scenario::scenario_name(int unsigned scenario_kind = 0);
   if (!this.scenario_names.exists(scenario_kind)) begin
      vmm_log log = this.get_vmm_log();
      if (this.next_scenario_kind == 0 && scenario_kind == 0) begin
         return this.__default_name();
      end
      `vmm_error(log, `vmm_sformatf("Cannot find scenario name: undefined scenario kind %0d",
                                    scenario_kind));
      return "?";
   end

   scenario_name = this.scenario_names[scenario_kind];
endfunction: scenario_name


function string vmm_scenario::__default_name();
   return "Undefined VMM Scenario";
endfunction: __default_name


function int unsigned vmm_scenario::get_max_length();
   return this.max_length;
endfunction: get_max_length


function void vmm_scenario::set_parent_scenario(vmm_scenario parent);
   this.parent = parent;
endfunction: set_parent_scenario


function vmm_scenario vmm_scenario::get_parent_scenario();
   return this.parent;
endfunction: get_parent_scenario


function vmm_data vmm_scenario::copy(vmm_data to = null);
   vmm_scenario cpy;

   if (to == null) cpy = new;
   else if (!$cast(cpy, to)) begin
      vmm_log log = this.get_vmm_log();
      `vmm_fatal(log, "Cannot copy to non-vmm_scenario instance");
      return null;
   end

   super.copy_data(cpy);

   cpy.next_scenario_kind = this.next_scenario_kind;
   cpy.max_length         = this.max_length;
   cpy.scenario_names     = this.scenario_names;
   cpy.parent             = this.parent;


   cpy.scenario_kind = this.scenario_kind;
   cpy.length        = this.length;
   cpy.repeated      = this.repeated;

   return cpy;
endfunction: copy
