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
`ifndef TUE_COMPONENT_PROXY_SVH
`define TUE_COMPONENT_PROXY_SVH
const string  TUE_NAME_OF_COMPONENT_PROXY = "component_proxy";

virtual class tue_component_proxy_base #(
  type  CONFIGURATION = tue_configuration_dummy,
  type  STATUS        = tue_status_dummy
) extends uvm_component;
  typedef tue_component_proxy_base #(CONFIGURATION, STATUS) this_type;

  static function this_type get(uvm_component component);
    this_type component_proxy;
    if (component == null) begin
      return null;
    end
    if (!component.has_child(TUE_NAME_OF_COMPONENT_PROXY)) begin
      return null;
    end
    if (!$cast(component_proxy, component.get_child(TUE_NAME_OF_COMPONENT_PROXY))) begin
      return null;
    end
    return component_proxy;
  endfunction

  pure virtual function void set_configuration(tue_configuration configuration);
  pure virtual function CONFIGURATION get_configuration();
  pure virtual function void set_status(tue_status status);
  pure virtual function STATUS get_status();
  pure virtual function void set_context(tue_configuration configuration, tue_status status);

  `tue_component_default_constructor(tue_component_proxy_base)
endclass

class tue_component_proxy #(
  type  COMPONENT     = uvm_component,
  type  CONFIGURATION = tue_configuration_dummy,
  type  STATUS        = tue_status_dummy
) extends tue_component_proxy_base #(CONFIGURATION, STATUS);
  typedef tue_component_proxy #(COMPONENT, CONFIGURATION, STATUS) this_type;

  local COMPONENT component;

  static function this_type create_component_proxy(COMPONENT component);
    this_type component_proxy;
    component_proxy = new(TUE_NAME_OF_COMPONENT_PROXY, component);
    return component_proxy;
  endfunction

  function new(string name = "tue_component_proxy", uvm_component parent = null);
    super.new(name, parent);
    $cast(component, parent);
  endfunction

  function void set_configuration(tue_configuration configuration);
    component.set_configuration(configuration);
  endfunction

  function CONFIGURATION get_configuration();
    return component.get_configuration();
  endfunction

  function void set_status(tue_status status);
    component.set_status(status);
  endfunction

  function STATUS get_status();
    return component.get_status();
  endfunction

  function void set_context(tue_configuration configuration, tue_status status);
    component.set_context(configuration, status);
  endfunction
endclass
`endif
