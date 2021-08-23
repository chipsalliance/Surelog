/*********************************************************************************
Copyright (c) 2021 Wavious LLC

This program is free software: you can redistribute it and/or modify
it under the terms of the GNU General Public License as published by
the Free Software Foundation, either version 3 of the License, or
(at your option) any later version.

This program is distributed in the hope that it will be useful,
but WITHOUT ANY WARRANTY; without even the implied warranty of
MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
GNU General Public License for more details.

You should have received a copy of the GNU General Public License
along with this program.  If not, see <http://www.gnu.org/licenses/>.

*********************************************************************************/

// HINT: Here you update the version.
`define wav_APB_VERSION "1.0"

typedef enum bit {APB_READ=0, APB_WRITE=1} apb_direction_enum;

`define reg_write(REG_NAME, VALUE) \
  write_reg = reg_model.get_reg_by_name(REG_NAME);\
  write_reg.write(status,VALUE); \
  `uvm_info("REG_SEQ", $sformatf("%s WRITE:0x%h",write_reg.get_name(), VALUE),UVM_DEBUG);

`define reg_read(REG_NAME, VALUE) \
  read_reg = reg_model.get_reg_by_name(REG_NAME);\
  read_reg.read(status,VALUE); \
  `uvm_info("REG_SEQ", $sformatf("%s READ:0x%h",read_reg.get_name(), VALUE),UVM_DEBUG); \

`define reg_write_by_field(REG_NAME, REG_FIELD, VALUE) \
  write_reg = reg_model.get_reg_by_name(REG_NAME);\
  write_reg.read(status, VAL); \
  VAL[REG_FIELD] = VALUE; \
  write_reg.write(status,VALUE);
 //  `uvm_info("REG_SEQ", $sformatf("%s READ:0x%h",read_reg.get_name(), VALUE),UVM_DEBUG); \
