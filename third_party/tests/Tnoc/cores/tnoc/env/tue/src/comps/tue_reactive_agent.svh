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
`ifndef TUE_REACTIVE_AGENT_SVH
`define TUE_REACTIVE_AGENT_SVH
virtual class tue_reactive_agent #(
  type  CONFIGURATION = tue_configuration_dummy,
  type  STATUS        = tue_status_dummy,
  type  ITEM          = tue_sequence_item_dummy,
  type  MONITOR       = tue_monitor_dummy,
  type  SEQUENCER     = tue_sequencer_dummy,
  type  DRIVER        = tue_driver_dummy
) extends tue_param_agent #(CONFIGURATION, STATUS, ITEM, MONITOR, SEQUENCER, DRIVER);
  function void connect_phase(uvm_phase phase);
    super.connect_phase(phase);
    if (is_active_agent()) begin
      monitor.request_port.connect(sequencer.request_export);
    end
  endfunction

  `tue_component_default_constructor(tue_reactive_agent)
endclass
`endif
