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
class reg_reset_seq extends uvm_reg_sequence #(uvm_sequence #(uvm_reg_item));

    `uvm_object_utils(reg_reset_seq)

    function new(string name="reg_reset_seq");
        super.new(name);
    endfunction

    // Variable: model
    //
    // The block to be tested. Declared in the base class.
    //
    //| uvm_reg_block model;

    // Variable: body
    //
    // Executes the Hardware Reset sequence.
    // Do not call directly. Use seq.start() instead.

    virtual task body();

        uvm_reg regs[$];
        uvm_reg_map maps[$];
        int VALUE_NO_REG_TESTS;

        if (model == null) begin
            `uvm_error("reg_reset_seq", "Not block or system specified to run sequence on");
            return;
        end

    uvm_report_info("STARTING_SEQ",{"\n\nStarting ",get_name()," sequence...\n"},UVM_LOW);

    this.reset_blk(model);
    model.reset();
    model.get_maps(maps);

    // Iterate over all maps defined for the RegModel block

    foreach (maps[d]) begin

    // Iterate over all registers in the map, checking accesses
    // Note: if map were in inner loop, could test simulataneous
    // access to same reg via different bus interfaces

    regs.delete();
    maps[d].get_registers(regs);

    foreach (regs[i]) begin

    uvm_status_e status;

    uvm_resource_db#(bit)::read_by_name({"REG::",regs[i].get_full_name()},"NO_REG_TESTS", VALUE_NO_REG_TESTS, null);

        //`uvm_info(get_type_name(), $sformatf("REGISTER %s NO_REG_TESTS=%0d", regs[i].get_full_name(),VALUE_NO_REG_TESTS), UVM_HIGH);

        if ( VALUE_NO_REG_TESTS  == 1 ) begin
            VALUE_NO_REG_TESTS = 0;
        `uvm_info(get_type_name(),
            $sformatf("Skipping register %s in map \"%s\"...",
            regs[i].get_full_name(), maps[d].get_full_name()), UVM_LOW);
            continue;
        end

        `uvm_info(get_type_name(),
            $sformatf("Verifying reset value of register %s in map \"%s\"...",
            regs[i].get_full_name(), maps[d].get_full_name()), UVM_LOW);

            regs[i].mirror(status, UVM_CHECK, UVM_FRONTDOOR, maps[d], this);

            if (status != UVM_IS_OK) begin
                `uvm_error(get_type_name(),
                    $sformatf("Status was %s when reading reset value of register \"%s\" through map \"%s\".",
                    status.name(), regs[i].get_full_name(), maps[d].get_full_name()));
                end
            end
        end

    endtask: body

    virtual task reset_blk(uvm_reg_block blk);
    endtask

endclass: reg_reset_seq

class wddr_reg_reset_seq extends wddr_base_seq;

    `uvm_object_utils(wddr_reg_reset_seq)
    uvm_reg      regs[$];
    uvm_reg      temp_reg;

    reg_reset_seq rst_seq;

    function new(string name="wddr_reg_reset_seq");
        super.new(name);
    endfunction

    virtual task body();
        super.body();

        rst_seq       = reg_reset_seq::type_id::create("rst_seq");
        rst_seq.model = this.reg_model;
        reg_model.get_registers(regs);

        foreach(regs[i]) begin
            temp_reg = regs[i];
            if(temp_reg.get_rights() == "RO" ) begin
            `uvm_info("RO REG", $sformatf("RO Registers Masked : %s",regs[i].get_name()),UVM_LOW)
            uvm_resource_db#(bit)::set({"REG::",temp_reg.get_full_name()},"NO_REG_TESTS", 1, this);
            end
        end
        reg_model.reset("HARD");

        rst_seq.start(null,this);

        #100ns;

        `uvm_info(get_type_name(), $sformatf("REG RESET TEST Completed !!!!!!!"),UVM_LOW)

    endtask : body

endclass
