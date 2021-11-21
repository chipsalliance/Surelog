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
`ifndef TUE_REG_ITEM_SVH
`define TUE_REG_ITEM_SVH
class tue_reg_item extends uvm_reg_item;
  uvm_reg_byte_en_t byte_en[];

  function new(string name = "tue_reg_item");
    super.new(name);
    byte_en = new[1];
  endfunction

  virtual function void do_copy(uvm_object rhs);
    tue_reg_item  _rhs;
    super.do_copy(rhs);
    if ((rhs != null) && $cast(_rhs, rhs)) begin
      byte_en = _rhs.byte_en;
    end
  endfunction

  `uvm_object_utils(tue_reg_item)
endclass
`endif
