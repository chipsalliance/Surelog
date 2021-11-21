//------------------------------------------------------------------------------
//  Copyright 2017 Taichi Ishitani
//
//  Licensed under the Apache License, Version 2.0 (the "License");
//  you may not use this file except in compliance with the License.
//  You may obtain a copy of the License at
//
//  http://www.apache.org/licenses/LICENSE-2.0
//
//  Unless required by applicable law or agreed to in writing, software
//  distributed under the License is distributed on an "AS IS" BASIS,
//  WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
//  See the License for the specific language governing permissions and
//  limitations under the License.
//------------------------------------------------------------------------------
`ifndef TUE_AGENT_SVH
`define TUE_AGENT_SVH
virtual class tue_agent #(
  type  CONFIGURATION = tue_configuration_dummy,
  type  STATUS        = tue_status_dummy
) extends tue_component_base #(uvm_agent, CONFIGURATION, STATUS);
  virtual function void active_agent();
    is_active = UVM_ACTIVE;
  endfunction

  virtual function void passive_agent();
    is_active = UVM_PASSIVE;
  endfunction

  virtual function bit is_active_agent();
    return (is_active == UVM_ACTIVE) ? 1 : 0;
  endfunction

  virtual function bit is_passive_agent();
    return (is_active == UVM_PASSIVE) ? 1 : 0;
  endfunction

  function void apply_config_settings(bit verbose = 0);
    super.apply_config_settings(verbose);
    apply_agent_mode();
  endfunction

  protected virtual function void apply_agent_mode();
  endfunction

  `tue_component_default_constructor(tue_agent)
endclass
`endif
