//------------------------------------------------------------------------------
//  Copyright 2020 Taichi Ishitani
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
`ifndef TUE_SEQUENCE_ITEM_DISPATCHER_SVH
`define TUE_SEQUENCE_ITEM_DISPATCHER_SVH
virtual class tue_sequence_item_dispatcher #(
  type  CONFIGURATION = tue_configuration_dummy,
  type  STATUS        = tue_status_dummy,
  type  ITEM          = uvm_sequence_item
) extends tue_sequence #(
  .CONFIGURATION  (CONFIGURATION  ),
  .STATUS         (STATUS         ),
  .REQ            (ITEM           )
);
  virtual task dispatch(
    ITEM              item,
    uvm_sequence_base parent_sequence = null
  );
    uvm_sequence_base   dispatcher;
    uvm_sequencer_base  sequencer[2];
    int                 sequence_id;

    dispatcher  = parent_sequence;
    if (dispatcher == null) begin
      dispatcher  = item.get_parent_sequence();
    end
    if (dispatcher == null) begin
      dispatcher  = this;
    end

    sequencer[0]  = select_sequencer(item);
    sequencer[1]  = item.get_sequencer();
    sequence_id   = item.get_sequence_id();
    dispatcher.start_item(item, -1, sequencer[0]);
    dispatcher.finish_item(item, -1);
    item.set_sequencer(sequencer[1]);
    item.set_sequence_id(sequence_id);

    post_dispatch(item);
  endtask

  protected virtual function uvm_sequencer_base select_sequencer(ITEM item);
    `uvm_fatal("TUE_SEQUENCE_ITEM_DISPATCHER", "select_sequencer is not implemented")
  endfunction

  protected virtual task post_dispatch(ITEM item);
  endtask

  `tue_object_default_constructor(tue_sequence_item_dispatcher)
endclass
`endif
