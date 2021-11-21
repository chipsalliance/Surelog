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
`ifndef TUE_SEQUENCE_BASE_SVH
`define TUE_SEQUENCE_BASE_SVH
class tue_sequence_base #(
  type  BASE                = uvm_sequence,
  type  CONFIGURATION       = tue_configuration_dummy,
  type  STATUS              = tue_status_dummy,
  type  PROXY_CONFIGURATION = CONFIGURATION,
  type  PROXY_STATUS        = STATUS
) extends tue_sequence_item_base #(
  BASE, CONFIGURATION, STATUS, PROXY_CONFIGURATION, PROXY_STATUS
);
`ifdef TUE_UVM_PRE_1_2
    protected bit enable_automatic_phase_objection  = 0;

    function void set_automatic_phase_objection(bit value);
      enable_automatic_phase_objection  = value;
    endfunction

    task pre_body();
      if ((starting_phase != null) && enable_automatic_phase_objection) begin
        starting_phase.raise_objection(this);
      end
    endtask

    task post_body();
      if ((starting_phase != null) && enable_automatic_phase_objection) begin
        starting_phase.drop_objection(this);
      end
    endtask
`else
  function void set_automatic_phase_objection(bit value);
    super.set_automatic_phase_objection(value);
  endfunction
`endif

  `tue_object_default_constructor(tue_sequence)
endclass
`endif
