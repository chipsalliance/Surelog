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

class wav_APB_transfer extends uvm_sequence_item;

  rand bit [31:0] data;
  rand bit [31:0] addr;
  rand apb_direction_enum direction;
  rand bit [2:0]    prot;
  rand bit [3:0]    strb;
  bit               err;

  constraint c_data {
    data inside {[0:255]};
  }

  // TODO Define the default constraints in wav_uart_wav_APB_transfer
  // For example:

  `uvm_object_utils_begin(wav_APB_transfer)
    // TODO Register the fields for wav_D2D_APB_transfer
    // For example:
    `uvm_field_int(data, UVM_DEFAULT)
    `uvm_field_int(addr, UVM_DEFAULT)
    `uvm_field_int(prot, UVM_DEFAULT)
    `uvm_field_int(strb, UVM_DEFAULT)
    `uvm_field_int(err, UVM_DEFAULT)
    `uvm_field_enum(apb_direction_enum, direction, UVM_DEFAULT)
  `uvm_object_utils_end

  // new - constructor
  function new (string name = "wav_APB_transfer_inst");
    super.new(name);
  endfunction

endclass
