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
`ifndef wddr_mcu_load_mem_test
`define wddr_mcu_load_mem_test

// ****************************************************************************
// Class : baseTest
// Desc. : Send a basic DFI frame
// ****************************************************************************
class wddr_mcu_load_mem_test extends wddr_base_test;

    //cdnDfimcUvmUserSve dfimcSve0;
    reg[7:0] data_A[];
    reg[7:0] data_B[];

    `uvm_component_utils_begin(wddr_mcu_load_mem_test)
    `uvm_component_utils_end

    function new(string name = "wddr_mcu_load_mem_test",uvm_component parent);
        super.new(name,parent);
    endfunction : new

    virtual function void build_phase(uvm_phase phase);
        super.build_phase(phase);
        //set the starting sequence to system

    endfunction : build_phase

    task run_phase(uvm_phase phase);

        uvm_objection objection;

        wddr_mcu_load_mem loadmem_seq;

        phase.raise_objection(this, "start_test");

        super.run_phase(phase);

        loadmem_seq  = wddr_mcu_load_mem::type_id::create("loadmem_seq");
        loadmem_seq.start(null);

        `uvm_info(get_type_name(),$psprintf("------- Load Mem Done ---------"), UVM_LOW)

        phase.drop_objection(this,"Done test.");

    endtask

endclass : wddr_mcu_load_mem_test

`endif
