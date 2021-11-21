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
`ifndef TUE_ITEM_WAITER_SVH
`define TUE_ITEM_WAITER_SVH
virtual class tue_item_waiter #(
  type  CONFIGURATION = uvm_object,
  type  STATUS        = uvm_object,
  type  ITEM          = uvm_sequence_item,
  type  ID            = int
) extends tue_subscriber #(
  .CONFIGURATION  (CONFIGURATION  ),
  .STATUS         (STATUS         ),
  .T              (ITEM           )
);
  local uvm_event waiters[$];
  local uvm_event id_waiters[ID][$];

  function void write(ITEM t);
    ID  id  = get_id(t);

    foreach (waiters[i]) begin
      waiters[i].trigger(t);
    end
    waiters.delete();

    if (!id_waiters.exists(id)) begin
      return;
    end

    foreach (id_waiters[id][i]) begin
      id_waiters[id][i].trigger(t);
    end
    id_waiters.delete(id);
  endfunction

  virtual task get_item(ref ITEM item);
    uvm_event waiter  = get_waiter();
    waiter.wait_on();
    $cast(item, waiter.get_trigger_data());
  endtask

  virtual task get_item_by_id(input ID id, ref ITEM item);
    uvm_event waiter  = get_id_waiter(id);
    waiter.wait_on();
    $cast(item, waiter.get_trigger_data());
  endtask

  protected virtual function ID get_id(ITEM item);
    `uvm_fatal("TUE_ITEM_WAITER", "get_id is not implemented")
  endfunction

  local function uvm_event get_waiter();
    uvm_event waiter  = new();
    waiters.push_back(waiter);
    return waiter;
  endfunction

  local function uvm_event get_id_waiter(ID id);
    uvm_event waiter  = new();
    id_waiters[id].push_back(waiter);
    return waiter;
  endfunction

  `tue_component_default_constructor(tue_item_waiter)
endclass
`endif
