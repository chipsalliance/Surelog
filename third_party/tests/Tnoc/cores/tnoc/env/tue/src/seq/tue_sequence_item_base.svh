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
`ifndef TUE_SEQUENCE_ITEM_BASE_SVH
`define TUE_SEQUENCE_ITEM_BASE_SVH
class tue_sequence_item_base #(
  type  BASE                = uvm_sequence_item,
  type  CONFIGURATION       = tue_configuration_dummy,
  type  STATUS              = tue_status_dummy,
  type  PROXY_CONFIGURATION = CONFIGURATION,
  type  PROXY_STATUS        = STATUS
) extends tue_object_base #(
  BASE, CONFIGURATION, STATUS
);
  typedef tue_component_proxy_base #(
    PROXY_CONFIGURATION, PROXY_STATUS
  ) t_component_proxy;

  function void set_sequencer(uvm_sequencer_base sequencer);
    t_component_proxy component_proxy;
    super.set_sequencer(sequencer);
    component_proxy = t_component_proxy::get(sequencer);
    if (component_proxy != null) begin
      set_context(component_proxy.get_configuration(), component_proxy.get_status());
    end
  endfunction

  function uvm_event get_event(string name);
    uvm_event_pool  event_pool  = get_event_pool();
    return event_pool.get(name);
  endfunction

  function bit began();
    uvm_event event_handle  = get_event("begin");
    return event_handle.is_on();
  endfunction

  function bit ended();
    uvm_event event_handle  = get_event("end");
    return event_handle.is_on();
  endfunction

  task wait_for_beginning(bit delta = 0);
    uvm_event begin_event = get_event("begin");
    begin_event.wait_on(delta);
  endtask

  task wait_for_ending(bit delta = 0);
    uvm_event end_event = get_event("end");
    end_event.wait_on(delta);
  endtask

  `tue_object_default_constructor(tue_sequence_item_base)
endclass
`endif
