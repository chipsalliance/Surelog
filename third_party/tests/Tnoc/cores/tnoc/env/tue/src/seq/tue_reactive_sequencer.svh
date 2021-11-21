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
`ifndef TUE_REACTIVE_SEQUENCER_SVH
`define TUE_REACTIVE_SEQUENCER_SVH

`uvm_analysis_imp_decl(_request)

virtual class tue_reactive_sequencer_base #(
  type  CONFIGURATION       = tue_configuration_dummy,
  type  STATUS              = tue_status_dummy,
  type  ITEM                = uvm_sequence_item,
  type  REQUEST             = ITEM,
  type  RSP                 = ITEM,
  type  PROXY_CONFIGURATION = CONFIGURATION,
  type  PROXY_STATUS        = STATUS
) extends tue_sequencer #(
  .CONFIGURATION        (CONFIGURATION        ),
  .STATUS               (STATUS               ),
  .REQ                  (ITEM                 ),
  .RSP                  (RSP                  ),
  .PROXY_CONFIGURATION  (PROXY_CONFIGURATION  ),
  .PROXY_STATUS         (PROXY_STATUS         )
);
  virtual task get_request(ref REQUEST request);
    `uvm_fatal("TUE_REACTIVE_SEQUENCER", "get_request is not implemented.")
  endtask

  `tue_component_default_constructor(tue_reactive_sequencer_base)
endclass

virtual class tue_reactive_sequencer #(
  type  CONFIGURATION       = tue_configuration_dummy,
  type  STATUS              = tue_status_dummy,
  type  ITEM                = uvm_sequence_item,
  type  REQUEST             = ITEM,
  type  REQUEST_HANDLE      = REQUEST,
  type  RSP                 = ITEM,
  type  PROXY_CONFIGURATION = CONFIGURATION,
  type  PROXY_STATUS        = STATUS
) extends tue_reactive_sequencer_base #(
  .CONFIGURATION        (CONFIGURATION        ),
  .STATUS               (STATUS               ),
  .ITEM                 (ITEM                 ),
  .REQUEST              (REQUEST              ),
  .RSP                  (RSP                  ),
  .PROXY_CONFIGURATION  (PROXY_CONFIGURATION  ),
  .PROXY_STATUS         (PROXY_STATUS         )
);
  typedef tue_reactive_sequencer #(
    .CONFIGURATION        (CONFIGURATION        ),
    .STATUS               (STATUS               ),
    .ITEM                 (ITEM                 ),
    .REQUEST              (REQUEST              ),
    .REQUEST_HANDLE       (REQUEST_HANDLE       ),
    .RSP                  (RSP                  ),
    .PROXY_CONFIGURATION  (PROXY_CONFIGURATION  ),
    .PROXY_STATUS         (PROXY_STATUS         )
  ) this_type;

  uvm_analysis_imp_request #(REQUEST_HANDLE, this_type) request_export;

  function void build_phase(uvm_phase phase);
    super.build_phase(phase);
    request_export  = new("request_export", this);
  endfunction

  virtual function void write_request(REQUEST_HANDLE request);
    `uvm_fatal("TUE_REACTIVE_SEQUENCER", "write_request is not implemented.")
  endfunction

  `tue_component_default_constructor(tue_reactive_sequencer)
endclass

class tue_reactive_fifo_sequencer #(
  type  CONFIGURATION       = tue_configuration_dummy,
  type  STATUS              = tue_status_dummy,
  type  ITEM                = uvm_sequence_item,
  type  REQUEST             = ITEM,
  type  REQUEST_HANDLE      = ITEM,
  type  RSP                 = ITEM,
  type  PROXY_CONFIGURATION = CONFIGURATION,
  type  PROXY_STATUS        = STATUS
) extends tue_reactive_sequencer #(
  .CONFIGURATION        (CONFIGURATION        ),
  .STATUS               (STATUS               ),
  .ITEM                 (ITEM                 ),
  .REQUEST              (REQUEST              ),
  .REQUEST_HANDLE       (REQUEST_HANDLE       ),
  .RSP                  (RSP                  ),
  .PROXY_CONFIGURATION  (PROXY_CONFIGURATION  ),
  .PROXY_STATUS         (PROXY_STATUS         )
);
  protected uvm_tlm_analysis_fifo #(REQUEST)  request_fifo;

  function void build_phase(uvm_phase phase);
    super.build_phase(phase);
    request_fifo  = new("request_fifo", this);
  endfunction

  function void write_request(REQUEST_HANDLE request);
    request_fifo.write(request);
  endfunction

  task get_request(ref REQUEST request);
    REQUEST_HANDLE  temp;
    request_fifo.get(temp);
    $cast(request, temp);
  endtask

  `tue_component_default_constructor(tue_reactive_fifo_sequencer)
  `uvm_component_param_utils (tue_reactive_fifo_sequencer #(
    CONFIGURATION, STATUS, ITEM, REQUEST, RSP, PROXY_CONFIGURATION, PROXY_STATUS
  ))
endclass
`endif
