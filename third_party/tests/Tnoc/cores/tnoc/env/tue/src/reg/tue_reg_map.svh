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
`ifndef TUE_REG_MAP_SVH
`define TUE_REG_MAP_SVH
class tue_reg_message_demoter extends uvm_report_catcher;
  bit demote  = 0;

  function new(string name = "tue_reg_message_demoter");
    super.new(name);
  endfunction

  function action_e catch();
    uvm_severity  severity  = get_severity();
    string        id        = get_id();
    string        message   = get_message();

    if (
      demote                    &&
      (severity == UVM_WARNING) &&
      (id       == "RegModel" ) &&
      uvm_is_match("*does not seem to be initialized correctly*", message)
    ) begin
      set_action(UVM_NO_ACTION);
    end

    return THROW;
  endfunction
endclass

class tue_reg_map extends uvm_reg_map;
  static  protected tue_reg_message_demoter m_message_demoter;

  protected int unsigned      m_system_n_bytes;
  protected uvm_reg           m_regs_by_offset[uvm_reg_addr_t];
  protected uvm_reg           m_regs_by_offset_wo[uvm_reg_addr_t];
  protected uvm_mem           m_mems_by_offset[uvm_reg_map_addr_range];

  function new(string name = "tue_reg_map");
    super.new(name);
    if (m_message_demoter == null) begin
      m_message_demoter = new("message_demoter");
      uvm_report_cb::add(null, m_message_demoter);
    end
  endfunction

  virtual function void add_reg(
    uvm_reg           rg,
    uvm_reg_addr_t    offset,
    string            rights    = "RW",
    bit               unmapped  = 0,
    uvm_reg_frontdoor frontdoor = null
  );
    tue_reg temp;

    if ((frontdoor == null) && $cast(temp, rg)) begin
      frontdoor = temp.create_frontdoor();
    end

    super.add_reg(rg, offset, rights, unmapped, frontdoor);
  endfunction

  virtual function void m_set_reg_offset(uvm_reg rg, uvm_reg_addr_t offset, bit unmapped);
    uvm_reg_map_info  info;

    info  = get_reg_map_info_without_warning(rg);
    if (info == null) begin
      return;
    end

    if (is_parent_locked()) begin
      if (!info.unmapped) begin
        remove_cached_reg(rg, info);
      end
      if (!unmapped) begin
        void'(map_reg(rg, info, offset));
      end
    end

    if (unmapped) begin
      info.offset   = -1;
      info.unmapped = 1;
    end
    else begin
      info.offset   = offset;
      info.unmapped = 0;
    end
  endfunction

  virtual function void m_set_mem_offset(uvm_mem mem, uvm_reg_addr_t offset, bit unmapped);
    uvm_reg_map_info  info;

    info  = get_mem_map_info(mem, 1);
    if (info == null) begin
      return;
    end

    if (is_parent_locked()) begin
      if (!info.unmapped) begin
        remove_cached_mem(mem, info);
      end
      if (!unmapped) begin
        void'(map_mem(mem, info, offset));
      end
    end

    if (!unmapped) begin
      info.offset   = -1;
      info.unmapped = 1;
    end
    else begin
      info.offset   = offset;
      info.unmapped = 0;
    end
  endfunction

  virtual function int unsigned get_n_bytes(uvm_hier_e hier = UVM_HIER);
    if (hier == UVM_NO_HIER) begin
      return super.get_n_bytes(UVM_NO_HIER);
    end
    else begin
      return m_system_n_bytes;
    end
  endfunction

  virtual function void set_base_addr(uvm_reg_addr_t offset);
    super.set_base_addr(offset);
    if (is_parent_locked() && (get_parent_map() == null)) begin
      initialize_map(get_root_map());
    end
  endfunction

  virtual function void set_submap_offset(uvm_reg_map submap, uvm_reg_addr_t offset);
    super.set_submap_offset(submap, offset);
    if (is_parent_locked() && (get_parent_map() == null)) begin
      initialize_map(get_root_map());
    end
  endfunction

  virtual function uvm_reg get_reg_by_offset(uvm_reg_addr_t offset, bit read = 1);
    if (!is_parent_locked()) begin
      uvm_reg_block parent  = get_parent();
      `uvm_error(
        "RegModel",
        $sformatf(
          "Cannot get register by offset: Block %s is not locked.",
          parent.get_full_name()
        )
      )
      return null;
    end

    if ((!read) && m_regs_by_offset_wo.exists(offset)) begin
      return m_regs_by_offset_wo[offset];
    end

    if (m_regs_by_offset.exists(offset)) begin
      return m_regs_by_offset[offset];
    end

    return null;
  endfunction

  virtual function uvm_mem get_mem_by_offset(uvm_reg_addr_t offset);
    if (!is_parent_locked()) begin
      uvm_reg_block parent  = get_parent();
      `uvm_error(
        "RegModel",
        $sformatf(
          "Cannot memory register by offset: Block %s is not locked.",
          parent.get_full_name()
        )
      )
      return null;
    end

    foreach (m_mems_by_offset[range]) begin
      if ((offset >= range.min) && (offset <= range.max)) begin
        return m_mems_by_offset[range];
      end
    end

    return null;
  endfunction

  virtual function void initialize();
    uvm_reg_map   submaps[$];
    uvm_reg       regs[$];
    uvm_mem       mems[$];
    int unsigned  bus_width[2];

    if (get_root_map() == this) begin
      m_regs_by_offset.delete();
      m_regs_by_offset_wo.delete();
      m_mems_by_offset.delete();
    end

    get_submaps(submaps, UVM_NO_HIER);
    foreach (submaps[i]) begin
      initialize_map(submaps[i]);
    end

    get_registers(regs, UVM_NO_HIER);
    foreach (regs[i]) begin
      uvm_reg_map_info  info;

      info                = get_reg_map_info_without_warning(regs[i]);
      info.is_initialized = 1;
      if (info.unmapped) begin
        continue;
      end

      bus_width[0]  = map_reg(regs[i], info, info.offset);
      if (bus_width[0] > bus_width[1]) begin
        bus_width[1]  = bus_width[0];
      end
    end

    get_memories(mems, UVM_NO_HIER);
    foreach (mems[i]) begin
      uvm_reg_map_info  info;

      info  = get_mem_map_info(mems[i]);
      if ((info == null) || info.unmapped) begin
        continue;
      end

      bus_width[0]  = map_mem(mems[i], info, info.offset);
      if (bus_width[0] > bus_width[1]) begin
        bus_width[1]  = bus_width[0];
      end
    end

    if (bus_width[1] > 0) begin
      m_system_n_bytes  = bus_width[1];
    end
    else begin
      m_system_n_bytes  = get_n_bytes(UVM_NO_HIER);
    end
  endfunction

  protected function uvm_reg_map_info get_reg_map_info_without_warning(uvm_reg rg);
    uvm_reg_map_info  info;
    m_message_demoter.demote  = 1;
    info  = get_reg_map_info(rg, 1);
    m_message_demoter.demote  = 0;
    return info;
  endfunction

  protected function void initialize_map(uvm_reg_map map);
    tue_reg_map temp;
    if ($cast(temp, map)) begin
      temp.initialize();
    end
    else begin
      map.Xinit_address_mapX();
    end
  endfunction

  protected function void remove_cached_reg(uvm_reg rg, uvm_reg_map_info info);
    tue_reg_map root_map;
    void'($cast(root_map, get_root_map()));
    foreach (info.addr[i]) begin
      m_remove_cached_reg(root_map, rg, info.addr[i]);
    end
  endfunction

  protected virtual function void m_remove_cached_reg(tue_reg_map root_map, uvm_reg rg, uvm_reg_addr_t addr);
    if (root_map.m_regs_by_offset_wo.exists(addr)) begin
      if (root_map.m_regs_by_offset_wo[addr] == rg) begin
        //  rg is write only
        remove_write_only_cb(rg);
        remove_read_only_cb(root_map.m_regs_by_offset[addr]);
      end
      else begin
        //  rg is read only
        remove_read_only_cb(rg);
        remove_write_only_cb(root_map.m_regs_by_offset_wo[addr]);
        root_map.m_regs_by_offset[addr] = root_map.m_regs_by_offset_wo[addr];
      end
      root_map.m_regs_by_offset_wo.delete(addr);
    end
    else begin
      root_map.m_regs_by_offset.delete(addr);
    end
  endfunction

  protected function int unsigned map_reg(uvm_reg rg, uvm_reg_map_info info, uvm_reg_addr_t offset);
    tue_reg_map     root_map;
    int unsigned    bus_width;
    uvm_reg_addr_t  addrs[];

    void'($cast(root_map, get_root_map()));

    bus_width = get_physical_addresses(offset, 0, rg.get_n_bytes(), addrs);
    foreach (addrs[i]) begin
      m_map_reg(root_map, rg, addrs[i]);
      m_check_reg_addr(root_map, rg, addrs[i]);
    end

    info.addr     = addrs;
    info.unmapped = 0;

    return bus_width;
  endfunction

  protected virtual function void m_map_reg(tue_reg_map root_map, uvm_reg rg, uvm_reg_addr_t addr);
    if (!root_map.m_regs_by_offset.exists(addr)) begin
      root_map.m_regs_by_offset[addr] = rg;
    end
    else if (root_map.m_regs_by_offset[addr] != rg) begin
      uvm_reg   other_rg;
      bit [1:0] access[2];

      other_rg  = root_map.m_regs_by_offset[addr];
      access[0] = get_rg_access(rg);
      access[1] = get_rg_access(other_rg);

      if ((access[0] == 2'b01) && (access[1] == 2'b10)) begin
        //  rg is write only
        root_map.m_regs_by_offset_wo[addr]  = rg;
        add_write_only_cb(rg);
        add_read_only_cb(other_rg);
      end
      else if ((access[0] == 2'b10) && (access[1] == 2'b01)) begin
        //  rg is read only
        root_map.m_regs_by_offset[addr]     = rg;
        root_map.m_regs_by_offset_wo[addr]  = other_rg;
        add_read_only_cb(rg);
        add_write_only_cb(other_rg);
      end
    end
  endfunction

  protected virtual function void m_check_reg_addr(
    tue_reg_map     root_map,
    uvm_reg         rg,
    uvm_reg_addr_t  addr
  );
    if (
      root_map.m_regs_by_offset.exists(addr)     &&
      (root_map.m_regs_by_offset[addr]    != rg) &&
      (root_map.m_regs_by_offset_wo[addr] != rg)
    ) begin
      `uvm_warning(
        "RegModel",
        $sformatf(
          "In map '%s' register '%s' maps to same address as register '%s': 'h%0h",
          get_full_name(), rg.get_full_name(),
          root_map.m_regs_by_offset[addr].get_full_name(), addr
        )
      )
      return;
    end

    foreach (root_map.m_mems_by_offset[range]) begin
      if ((addr >= range.min) && (addr <= range.max)) begin
        `uvm_warning(
          "RegModel",
          $sformatf(
            "In map '%s' register '%s' overlaps with range of memory '%s': 'h%0h",
            get_full_name(), rg.get_full_name(),
            root_map.m_mems_by_offset[range].get_full_name(), addr
          )
        )
        return;
      end
    end
  endfunction

  protected function bit [1:0] get_rg_access(uvm_reg rg);
    tue_reg temp;
    if ($cast(temp, rg)) begin
      return {temp.is_readable(this), temp.is_writable(this)};
    end
    else begin
      case (rg.Xget_fields_accessX(this))
        "WO":     return 2'b01;
        "RO":     return 2'b10;
        default:  return 2'b11;
      endcase
    end
  endfunction

  protected virtual function void add_write_only_cb(uvm_reg rg);
    tue_reg_write_only_warning_cbs::add(rg);
  endfunction

  protected virtual function void remove_write_only_cb(uvm_reg rg);
    tue_reg_write_only_warning_cbs::remove(rg);
  endfunction

  protected virtual function void add_read_only_cb(uvm_reg rg);
    tue_reg_read_only_warning_cbs::add(rg);
  endfunction

  protected virtual function void remove_read_only_cb(uvm_reg rg);
    tue_reg_read_only_warning_cbs::remove(rg);
  endfunction

  protected function void remove_cached_mem(uvm_mem mem, uvm_reg_map_info info);
    tue_reg_map             root_map;
    uvm_reg_map_addr_range  target_ranges[$];

    void'($cast(root_map, get_root_map()));
    foreach (root_map.m_mems_by_offset[range]) begin
      if (root_map.m_mems_by_offset[range] == mem) begin
        target_ranges.push_back(range);
      end
    end

    foreach (target_ranges[i]) begin
      root_map.m_mems_by_offset.delete(target_ranges[i]);
    end
  endfunction

  protected function int unsigned map_mem(uvm_mem mem, uvm_reg_map_info info, uvm_reg_addr_t offset);
    uvm_reg_addr_t          addrs[];
    int unsigned            stride;
    tue_reg_map             root_map;
    int unsigned            bus_width[2];
    uvm_reg_map_addr_range  range;

    range.stride  = mem.get_n_bytes() / get_addr_unit_bytes();
    bus_width[0]  = get_physical_addresses(offset, 0, mem.get_n_bytes(), addrs);
    range.max     = (addrs[0] > addrs[addrs.size()-1]) ? addrs[0] : addrs[addrs.size()-1];
    bus_width[1]  = get_physical_addresses(offset, mem.get_size() - 1, mem.get_n_bytes(), addrs);
    range.min     = (addrs[0] < addrs[addrs.size()-1]) ? addrs[0] : addrs[addrs.size()-1];

    void'($cast(root_map, get_root_map()));
    m_map_mem(root_map, mem, range);
    m_check_mem_addr(root_map, mem, range);

    info.addr       = addrs;
    info.mem_range  = range;
    info.unmapped   = 0;

    return bus_width[0];
  endfunction

  protected virtual function void m_map_mem(
    tue_reg_map             root_map,
    uvm_mem                 mem,
    uvm_reg_map_addr_range  range
  );
    root_map.m_mems_by_offset[range]  = mem;
  endfunction

  protected virtual function void m_check_mem_addr(
    tue_reg_map             root_map,
    uvm_mem                 mem,
    uvm_reg_map_addr_range  mem_range
  );
    foreach (root_map.m_regs_by_offset[addr]) begin
      if ((addr >= mem_range.min) && (addr <= mem_range.max)) begin
        `uvm_warning(
          "RegModel",
          $sformatf(
            {
              "In map '%s' memory '%s' with [%0h:%0h] overlaps with ",
              "address of existing register: 'h%0h"
            },
            get_full_name(), mem.get_full_name(), mem_range.min, mem_range.max, addr
          )
        )
        return;
      end
    end

    foreach (root_map.m_mems_by_offset[range]) begin
      if (
        ((mem_range.min >= range.min    ) && (mem_range.min <= range.max    )) ||
        ((range.min     >= mem_range.min) && (range.min     <= mem_range.max))
      ) begin
        `uvm_warning(
          "RegModel",
          $sformatf(
            {
              "In map '%s' memory '%s' with range [%0h:%0h] overlaps ",
              "existing memory with range '%s': [%h0:%0h]"
            },
            get_full_name(), mem.get_full_name(), mem_range.min, mem_range.max,
            root_map.m_mems_by_offset[range].get_full_name(), range.min, range.max
          )
        )
        return;
      end
    end
  endfunction

  protected function bit is_parent_locked();
    uvm_reg_block parent_1;
    tue_reg_block parent_2;

    parent_1  = get_parent();
    if ($cast(parent_2, parent_1)) begin
      return parent_2.is_locked();
    end
    else begin
      return parent_1.is_locked();
    end
  endfunction

  `uvm_object_utils(tue_reg_map)
endclass
`endif
