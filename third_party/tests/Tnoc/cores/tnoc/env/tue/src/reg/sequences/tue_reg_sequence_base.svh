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
`ifndef TUE_REG_SEQUENCE_BASE_SVH
`define TUE_REG_SEQUENCE_BASE_SVH
class tue_reg_sequence_base #(
  type  BASE  = uvm_reg_sequence #(uvm_sequence #(uvm_reg_item))
) extends BASE;
  protected function bit is_field_writable(uvm_reg_field field, uvm_reg_map map = null);
    tue_reg_field temp;
    if ($cast(temp, field)) begin
      return temp.is_writable(map);
    end
    else begin
      string  access  = field.get_access(map);
      return !(access inside {"NOACCESS", "RO", "RC", "RS"});
    end
  endfunction

  protected function bit is_field_readable(uvm_reg_field field, uvm_reg_map map = null);
    tue_reg_field temp;
    if ($cast(temp, field)) begin
      return temp.is_readable(map);
    end
    else begin
      string  access  = field.get_access(map);
      return !(access inside {"NOACCESS", "WO", "WOC", "WOS", "WO1"});
    end
  endfunction

  protected function bit is_reg_writable(uvm_reg rg, uvm_reg_map map = null);
    uvm_reg_field fields[$];

    rg.get_fields(fields);
    foreach (fields[i]) begin
      if (is_field_writable(fields[i], map)) begin
        return 1;
      end
    end

    return 0;
  endfunction

  protected function bit is_reg_readable(uvm_reg rg, uvm_reg_map map = null);
    uvm_reg_field fields[$];

    rg.get_fields(fields);
    foreach (fields[i]) begin
      if (is_field_readable(fields[i], map)) begin
        return 1;
      end
    end

    return 0;
  endfunction

  protected function bit is_reg_test_executed(uvm_object element, string test_name);
    string  key = $sformatf("REG::%s", element.get_full_name());
    if (uvm_resource_db #(bit)::get_by_name(key, "NO_REG_TESTS", 0) != null) begin
      return 0;
    end
    else if (uvm_resource_db #(bit)::get_by_name(key, {"NO_", test_name}, 0) != null) begin
      return 0;
    end
    else begin
      return 1;
    end
  endfunction

  `tue_object_default_constructor(tue_reg_sequence_base)
endclass
`endif
