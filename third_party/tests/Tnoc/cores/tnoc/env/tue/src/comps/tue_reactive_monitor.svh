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
`ifndef TUE_REACTIVE_MONITOR_SVH
`define TUE_REACTIVE_MONITOR_SVH
virtual class tue_reactive_monitor #(
  type  CONFIGURATION = tue_configuration_dummy,
  type  STATUS        = tue_status_dummy,
  type  ITEM          = uvm_sequence_item,
  type  ITEM_HANDLE   = ITEM,
  type  REQUEST       = ITEM
) extends tue_param_monitor #(CONFIGURATION, STATUS, ITEM, ITEM_HANDLE);
  uvm_analysis_port #(REQUEST)  request_port;

  function void build_phase(uvm_phase phase);
    super.build_phase(phase);
    request_port  = new("request_port", this);
  endfunction

  function void write_request(uvm_object request);
    REQUEST r;
    if ($cast(r, request)) begin
      request_port.write(r);
    end
    else begin
      `uvm_fatal(get_name(), "Error casting request object")
    end
  endfunction

  `tue_component_default_constructor(tue_reactive_monitor)
endclass
`endif
