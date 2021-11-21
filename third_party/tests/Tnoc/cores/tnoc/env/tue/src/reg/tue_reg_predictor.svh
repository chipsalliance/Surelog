//------------------------------------------------------------------------------
//  Copyright 2019 Taichi Ishitani
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
`ifndef TUE_REG_PREDICTOR_SVH
`define TUE_REG_PREDICTOR_SVH
class tue_reg_predictor #(type BUSTYPE = int) extends uvm_reg_predictor #(BUSTYPE);
  function new(string name = "tue_reg_predictor", uvm_component parent = null);
    super.new(name, parent);
  endfunction

  function void start_of_simulation_phase(uvm_phase phase);
    super.start_of_simulation_phase(phase);
    if (adapter == null) begin
      `uvm_fatal("REG/PREDICTOR", "adapter handle is null")
    end
  endfunction

  virtual function void write(BUSTYPE tr);
    uvm_reg           rg;
    uvm_reg_bus_op    rw;
    bit               is_read;
    uvm_reg_map       local_map;
    uvm_reg_map_info  map_info;
    tue_reg_item      reg_item;
    uvm_reg           actual_rg;

    rw.byte_en  = '1;
    adapter.bus2reg(tr, rw);
    is_read = (rw.kind == UVM_READ) ? 1 : 0;

    rg  = map.get_reg_by_offset(rw.addr, is_read);
    if (rg == null) begin
      `uvm_info(
        "REG/PREDICTOR/NOT_FOR_ME",
        $sformatf("Observed transaction does not target a register %p", tr),
        UVM_FULL
      )
      return;
    end

    local_map   = rg.get_local_map(map);
    map_info    = local_map.get_reg_map_info(rg);
    reg_item    = create_reg_item(rg, rw, map_info);
    begin
      uvm_reg_indirect_data indirect;
      actual_rg = ($cast(indirect, rg)) ? indirect.get_indirect_reg() : rg;
    end

    if (is_read && local_map.get_check_on_read() && (reg_item.status != UVM_NOT_OK)) begin
      void'(rg.do_check(actual_rg.get_mirrored_value(), reg_item.value[0], local_map));
    end

    pre_predict(reg_item);
    do_sample(actual_rg, rg.get_parent(), reg_item, local_map, map_info);
    rg.do_predict(reg_item, (is_read) ? UVM_PREDICT_READ : UVM_PREDICT_WRITE, reg_item.byte_en[0]);

    reg_ap.write(reg_item);
  endfunction

  protected function tue_reg_item create_reg_item(
    input     uvm_reg           rg,
    const ref uvm_reg_bus_op    rw,
    input     uvm_reg_map_info  map_info
  );
    int           addr_index;
    tue_reg_item  reg_item;
    int           n_bytes;

    addr_index  = -1;
    foreach (map_info.addr[i]) begin
      if (rw.addr == map_info.addr[i]) begin
        addr_index  = i;
        break;
      end
    end
    if (addr_index < 0) begin
      `uvm_fatal(
        "REG/PREDICTOR/INTERNAL",
        $sformatf("Unexpected failed address lookup for register '%s'", rg.get_full_name())
      )
    end

    n_bytes               = map.get_n_bytes();
    reg_item              = new();
    reg_item.element_kind = UVM_REG;
    reg_item.element      = rg;
    reg_item.path         = UVM_PREDICT;
    reg_item.map          = map;
    reg_item.kind         = rw.kind;
    reg_item.value[0]     = rw.data << (addr_index * n_bytes * 8);
    reg_item.byte_en[0]   = (rw.byte_en & ((1 << n_bytes) - 1)) << (addr_index * n_bytes);
    reg_item.status       = rw.status;

    return reg_item;
  endfunction

  protected function void do_sample(
    uvm_reg           rg,
    uvm_reg_block     parent,
    tue_reg_item      reg_item,
    uvm_reg_map       local_map,
    uvm_reg_map_info  map_info
  );
    bit is_read = (reg_item.kind == UVM_READ) ? 1 : 0;
    rg.XsampleX(reg_item.value[0], reg_item.byte_en[0], is_read, local_map);
    parent.XsampleX(map_info.offset, is_read, local_map);
  endfunction

  `uvm_component_param_utils(tue_reg_predictor #(BUSTYPE))
endclass
`endif
