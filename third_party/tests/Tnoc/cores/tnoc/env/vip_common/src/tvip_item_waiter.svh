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
`ifndef TVIP_ITEM_WAITER_SVH
`define TVIP_ITEM_WAITER_SVH
class tvip_item_waiter #(
  type  ITEM  = uvm_sequence_item,
  type  ID    = int
) extends uvm_subscriber #(ITEM);
  protected uvm_event waiters[$];
  protected uvm_event id_waiters[ID][$];

  function void write(ITEM t);
    ID  id;

    foreach (waiters[i]) begin
      waiters[i].trigger(t);
    end
    waiters.delete();

    id  = get_id_from_item(t);
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
    wait_for_trigger(waiter, item);
  endtask

  virtual task get_item_by_id(ref ITEM item, input ID id);
    uvm_event waiter  = get_id_waiter(id);
    wait_for_trigger(waiter, item);
  endtask

  protected virtual function ID get_id_from_item(ITEM item);
    ID  id;
    return id;
  endfunction

  protected function uvm_event get_waiter();
    uvm_event waiter  = new();
    waiters.push_back(waiter);
    return waiter;
  endfunction

  protected function uvm_event get_id_waiter(ID id);
    uvm_event waiter  = new();
    id_waiters[id].push_back(waiter);
    return waiter;
  endfunction

  protected task wait_for_trigger(input uvm_event waiter, ref ITEM item);
    waiter.wait_on();
    void'($cast(item, waiter.get_trigger_data()));
  endtask

  `tue_component_default_constructor(tvip_item_waiter)
endclass
`endif
