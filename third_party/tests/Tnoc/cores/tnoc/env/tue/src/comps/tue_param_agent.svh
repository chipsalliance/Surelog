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
`ifndef TUE_PARAM_AGENT_SVH
`define TUE_PARAM_AGENT_SVH
class tue_sequence_item_dummy extends tue_sequence_item;
  `tue_object_default_constructor(tue_sequence_item_dummy)
  `uvm_object_utils(tue_sequence_item_dummy)
endclass

class tue_monitor_dummy extends tue_param_monitor #(.ITEM(tue_sequence_item_dummy));
  `tue_component_default_constructor(tue_monitor_dummy)
  `uvm_component_utils(tue_monitor_dummy)
endclass

class tue_sequencer_dummy extends tue_sequencer #(.REQ(tue_sequence_item_dummy));
  `tue_component_default_constructor(tue_sequencer_dummy)
  `uvm_component_utils(tue_sequencer_dummy)
endclass

class tue_driver_dummy extends tue_driver #(.REQ(tue_sequence_item_dummy));
  `tue_component_default_constructor(tue_driver_dummy)
  `uvm_component_utils(tue_driver_dummy)
endclass

virtual class tue_param_agent #(
  type  CONFIGURATION = tue_configuration_dummy,
  type  STATUS        = tue_status_dummy,
  type  ITEM          = tue_sequence_item_dummy,
  type  MONITOR       = tue_monitor_dummy,
  type  SEQUENCER     = tue_sequencer_dummy,
  type  DRIVER        = tue_driver_dummy
) extends tue_agent #(CONFIGURATION, STATUS);
  uvm_analysis_port #(ITEM) item_port;
  SEQUENCER                 sequencer;

  protected MONITOR monitor;
  protected DRIVER  driver;

  function void build_phase(uvm_phase phase);
    super.build_phase(phase);
    create_item_port();
    create_monitor();
    create_seqnecer();
    create_driver();
  endfunction

  function void connect_phase(uvm_phase phase);
    if ((item_port != null) && (monitor != null)) begin
      monitor.item_port.connect(item_port);
    end
    if ((sequencer != null) && (driver != null)) begin
      driver.seq_item_port.connect(sequencer.seq_item_export);
    end
  endfunction

  local function void create_item_port();
    if (!tue_check_type(ITEM::get_type(), tue_sequence_item_dummy::get_type())) begin
      item_port = new("item_port", this);
    end
  endfunction

  local function void create_monitor();
    if (!tue_check_type(MONITOR::get_type(), tue_monitor_dummy::get_type())) begin
      monitor = MONITOR::type_id::create("monitor", this);
      monitor.set_context(get_configuration(), get_status());
    end
  endfunction

  local function void create_seqnecer();
    if (is_active_agent() && (!tue_check_type(SEQUENCER::get_type(), tue_sequencer_dummy::get_type()))) begin
      sequencer = SEQUENCER::type_id::create("sequencer", this);
      sequencer.set_context(get_configuration(), get_status());
    end
  endfunction

  local function void create_driver();
    if (is_active_agent() && (!tue_check_type(DRIVER::get_type(), tue_driver_dummy::get_type()))) begin
      driver  = DRIVER::type_id::create("driver", this);
      driver.set_context(get_configuration(), get_status());
    end
  endfunction

  `tue_component_default_constructor(tue_param_agent)
endclass
`endif
