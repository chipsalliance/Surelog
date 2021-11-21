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
`ifndef TUE_PARAM_MONITOR_SVH
`define TUE_PARAM_MONITOR_SVH
virtual class tue_param_monitor #(
  type  CONFIGURATION = tue_configuration_dummy,
  type  STATUS        = tue_status_dummy,
  type  ITEM          = uvm_sequence_item,
  type  ITEM_HANDLE   = ITEM
) extends tue_monitor #(CONFIGURATION, STATUS);
  uvm_analysis_port #(ITEM_HANDLE)  item_port;

  function void build_phase(uvm_phase phase);
    super.build_phase(phase);
    item_port = new("item_port", this);
  endfunction

  virtual function ITEM_HANDLE create_item(
    string  item_name     = "item",
    string  stream_name   = "main",
    string  label         = "",
    string  desc          = "",
    time    begin_time    = 0,
    int     parent_handle = 0
  );
    ITEM  item;
    item  = ITEM::type_id::create(item_name);
    item.set_context(configuration, status);
    void'(begin_tr(item, stream_name, label, desc, begin_time, parent_handle));
    return item;
  endfunction

  virtual function void write_item(
    ITEM_HANDLE item,
    time        end_time    = 0,
    bit         free_handle = 1
  );
    uvm_event_pool  event_pool  = item.get_event_pool();
    uvm_event       end_event   = event_pool.get("end");
    if (!end_event.is_on()) begin
      end_tr(item, end_time, free_handle);
    end
    item_port.write(item);
  endfunction

  `tue_component_default_constructor(tue_param_monitor)
endclass
`endif
