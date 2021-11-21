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
`ifndef TUE_REG_FIELD_SVH
`define TUE_REG_FIELD_SVH
class tue_reg_field extends uvm_reg_field;
  virtual function void do_predict(
    uvm_reg_item      rw,
    uvm_predict_e     kind  = UVM_PREDICT_DIRECT,
    uvm_reg_byte_en_t be    = '1
  );
    uvm_reg_data_t  mask;
    uvm_reg_data_t  active_bits;
    uvm_reg_data_t  rw_value;
    uvm_reg_data_t  current_value;

    current_value = get_mirrored_value();
    mask          = (1 << get_n_bits()) - 1;
    active_bits   = get_active_bits(be, mask);
    rw_value      = rw.value[0] & mask;

    if (active_bits == '0) begin
      return;
    end

    if (kind != UVM_PREDICT_DIRECT) begin
      pre_predict(current_value, rw_value, kind, rw.path, rw.map);
      process_pre_predict_cbs(current_value, rw_value, kind, rw.path, rw.map);

      if (rw.path inside {UVM_FRONTDOOR, UVM_PREDICT}) begin
        if (!m_do_predict(current_value, rw_value, kind, rw.map)) begin
          return;
        end
      end

      post_predict(current_value, rw_value, kind, rw.path, rw.map);
    end

    begin
      uvm_reg_data_t  value;
      uvm_door_e      path;

      value = rw.value[0];
      path  = rw.path;

      rw.value[0] = ((rw_value & active_bits) | (current_value & (~active_bits))) & mask;
      rw.path     = UVM_DEFAULT_DOOR;
      super.do_predict(rw, kind, -1);

      rw.value[0] = value;
      rw.path     = path;
    end
  endfunction

  protected virtual function void pre_predict(
    input uvm_reg_data_t  current_value,
    inout uvm_reg_data_t  rw_value,
    input uvm_predict_e   kind,
    input uvm_door_e      path,
    input uvm_reg_map     map
  );
  endfunction

  protected virtual function void post_predict(
    input uvm_reg_data_t  current_value,
    inout uvm_reg_data_t  rw_value,
    input uvm_predict_e   kind,
    input uvm_door_e      path,
    input uvm_reg_map     map
  );
  endfunction

  protected function uvm_reg_data_t get_active_bits(
    uvm_reg_byte_en_t be,
    uvm_reg_data_t    mask
  );
    uvm_reg_data_t  bits;
    int unsigned    byte_width;
    int unsigned    bit_index;

    byte_width  = ((get_lsb_pos() % 8) + get_n_bits() + 7) / 8;
    bits        = '0;
    for (int i = 0;i < byte_width;++i) begin
      if (be[i]) begin
        bits[8*i+:8]  = '1;
      end
    end

    return bits & mask;
  endfunction

  protected function void process_pre_predict_cbs(
    input uvm_reg_data_t  current_value,
    inout uvm_reg_data_t  rw_value,
    input uvm_predict_e   kind,
    input uvm_door_e      path,
    input uvm_reg_map     map
  );
    uvm_reg_field_cb_iter cbs = new(this);
    for (uvm_reg_cbs cb = cbs.first();cb != null;cb = cbs.next()) begin
      tue_reg_cbs cb_temp;
      if ($cast(cb_temp, cb)) begin
        cb_temp.pre_predict(
          this, current_value, rw_value, kind, path, map
        );
      end
    end
  endfunction

  protected virtual function bit m_do_predict(
    input uvm_reg_data_t  current_value,
    ref   uvm_reg_data_t  rw_value,
    input uvm_predict_e   kind,
    input uvm_reg_map     map
  );
    if (kind == UVM_PREDICT_DIRECT) begin
      return 1;
    end
    else if (kind == UVM_PREDICT_WRITE) begin
      rw_value  = XpredictX(current_value, rw_value, map);
      return 1;
    end
    else begin
      string  access  = get_access(map);
      case (access)
        "RC", "WRC", "WSRC", "W1SRC", "W0SRC": begin
          rw_value  = '0; //  clear
          return 1;
        end
        "RS", "WRS", "WCRS", "W1CRS", "W0CRS": begin
          rw_value  = (1 << get_n_bits()) - 1;  //  all 1's
          return 1;
        end
        default: begin
          return is_readable(map);
        end
      endcase
    end
  endfunction

`ifdef TUE_UVM_PRE_IEEE
  virtual function string get_access(uvm_reg_map map = null);
    string  access;
    uvm_reg parent;

    access  = super.get_access(uvm_reg_map::backdoor());
    if (map == uvm_reg_map::backdoor()) begin
      return access;
    end

    parent  = get_parent();
    if (parent.get_rights(map) == "WO") begin
      case (access)
        "RW":     return "WO";
        "WRC":    return "WO";
        "WRS":    return "WO";
        "W1SRC":  return "W1S";
        "W0SRC":  return "W0S";
        "W1CRS":  return "W1C";
        "W0CRS":  return "W0C";
        "WCRS":   return "WC";
        "WSRC":   return "WS";
        "WO":     return access;
        "WC":     return access;
        "WS":     return access;
        "W1C":    return access;
        "W1S":    return access;
        "W0C":    return access;
        "W0S":    return access;
        "W0T":    return access;
        "W1":     return access;
        "WO1":    return access;
      endcase
    end

    return super.get_access(map);
  endfunction
`endif

  virtual function bit is_writable(uvm_reg_map map = null);
    string  access  = get_access(map);
    return !(access inside {"NOACCESS", "RO", "RC", "RS"});
  endfunction

  virtual function bit is_readable(uvm_reg_map map = null);
    string  access  = get_access(map);
    return !(access inside {"NOACCESS", "WO", "WOC", "WOS", "WO1"});
  endfunction

  `tue_object_default_constructor(tue_reg_field)
endclass
`endif
