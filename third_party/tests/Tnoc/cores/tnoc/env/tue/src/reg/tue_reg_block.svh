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
`ifndef TUE_REG_BLOCK_SVH
`define TUE_REG_BLOCK_SVH
typedef class tue_reg_map;

class tue_reg_block extends uvm_reg_block;
  protected bit locked;

  function new(string name = "", int has_coverage = UVM_NO_COVERAGE);
    super.new(name, has_coverage);
  endfunction

  virtual function bit is_locked();
    return locked;
  endfunction

  function void lock_model();
    uvm_reg       regs[$];
    uvm_mem       mems[$];
    uvm_reg_block blocks[$];
    uvm_reg_map   maps[$];
    uvm_reg_block parent;
    int           max_size;

    if (is_locked()) begin
      return;
    end
    locked  = 1;

    get_registers(regs, UVM_NO_HIER);
    foreach (regs[i]) begin
      regs[i].Xlock_modelX();
    end

    get_memories(mems, UVM_NO_HIER);
    foreach (mems[i]) begin
      mems[i].Xlock_modelX();
    end

    get_blocks(blocks, UVM_NO_HIER);
    foreach (blocks[i]) begin
      blocks[i].lock_model();
    end

    parent  = get_parent();
    if (parent != null) begin
      return;
    end

    max_size  = uvm_reg::get_max_size();
    if (uvm_reg_field::get_max_size() > max_size) begin
      max_size  = uvm_reg_field::get_max_size();
    end
    if (uvm_mem::get_max_size() > max_size) begin
      max_size  = uvm_mem::get_max_size();
    end
    if (max_size > `UVM_REG_DATA_WIDTH) begin
      `uvm_fatal(
        "RegModel",
        $sformatf(
          "Register model requires that UVM_REG_DATA_WIDTH be defined as %0d or greater. Currently defined as %0d",
          max_size, `UVM_REG_DATA_WIDTH
        )
      )
    end

    get_maps(maps);
    foreach (maps[i]) begin
      tue_reg_map map;
      if ($cast(map, maps[i])) begin
        map.initialize();
      end
      else begin
        maps[i].Xinit_address_mapX();
      end
    end
  endfunction

  virtual function uvm_reg_map create_map(
    string            name,
    uvm_reg_addr_t    base_addr,
    int unsigned      n_bytes,
    uvm_endianness_e  endian,
    bit               byte_addressing = 1
  );
    tue_reg_map map;

    map = tue_reg_map::type_id::create(name, null, get_full_name());
    map.configure(this, base_addr, n_bytes, endian, byte_addressing);
    add_map(map);

    return map;
  endfunction
endclass
`endif
