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
 class reg_to_apb_adapter extends uvm_reg_adapter;
    `uvm_object_utils(reg_to_apb_adapter)

    // The adapter to connect the register model to the sequencer

    function new (string name = "reg_to_apb_adapter");
      super.new(name);
      provides_responses = 1;
    endfunction

    function uvm_sequence_item reg2bus(const ref uvm_reg_bus_op rw);
      wav_APB_transfer transfer;

      transfer = wav_APB_transfer::type_id::create("transfer");
      transfer.addr      = rw.addr;
      transfer.data      = rw.data;
      transfer.direction = (rw.kind == UVM_READ) ? APB_READ : APB_WRITE;

      //`uvm_info(get_type_name(), $psprintf("reg2bus: Transfer Address:%h Data:%h Direction:%s",transfer.addr, transfer.data, transfer.direction), UVM_FULL)

      return transfer;
    endfunction

    function void bus2reg(uvm_sequence_item bus_item, ref uvm_reg_bus_op rw);
      wav_APB_transfer transfer;

      if(!$cast(transfer, bus_item) ) begin
        `uvm_fatal("NOT_REG_TYPE", "Incorrect bus item type. Expecting apb_transfer")
        return;
      end

        rw.kind = (transfer.direction==APB_WRITE) ? UVM_WRITE : UVM_READ;
        rw.addr = transfer.addr;
        rw.data = transfer.data;  // For monitoring, need write data as well as read data
        rw.status = UVM_IS_OK;

       // `uvm_info(get_type_name(), $psprintf("bus2reg: Transfer Address:%h Data:%h ",transfer.addr, transfer.data), UVM_FULL)

    endfunction

  endclass
