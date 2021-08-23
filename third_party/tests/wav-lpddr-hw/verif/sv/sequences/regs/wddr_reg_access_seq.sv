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
class reg_single_access_seq extends uvm_reg_sequence #(uvm_sequence #(uvm_reg_item));

    // Variable: rg
    // The register to be tested
    uvm_reg rg;

    `uvm_object_utils(reg_single_access_seq)

    function new(string name="reg_single_access_seq");
        super.new(name);
    endfunction

    virtual task body();
        uvm_reg_map maps[$];

        if (rg == null) begin
            `uvm_error("reg_access_seq", "No register specified to run sequence on")
            return;
        end

        // Registers with some attributes are not to be tested
        if (uvm_resource_db#(bit)::get_by_name({"REG::",rg.get_full_name()},
        "NO_REG_TESTS", 0) != null ||
        uvm_resource_db#(bit)::get_by_name({"REG::",rg.get_full_name()},
        "NO_REG_ACCESS_TEST", 0) != null )
        return;

        // Can only deal with registers with backdoor access
        if (rg.get_backdoor() == null && !rg.has_hdl_path()) begin
            `uvm_error("reg_access_seq", {"Register '",rg.get_full_name(),
            "' does not have a backdoor mechanism available"})
            return;
        end

        // Registers may be accessible from multiple physical interfaces (maps)
        rg.get_maps(maps);

        // Cannot test access if register contains RO or OTHER fields
        begin
            uvm_reg_field fields[$];

            rg.get_fields(fields);
            foreach (fields[j]) begin
                foreach (maps[k]) begin
                    if (fields[j].get_access(maps[k]) == "RO") begin
                        `uvm_warning("reg_access_seq", {"Register '",
                        rg.get_full_name(),"' has RO fields"})
                        return;
                    end
                    if (!fields[j].is_known_access(maps[k])) begin
                        `uvm_warning("reg_access_seq", {"Register '",rg.get_full_name(),
                            "' has field with unknown access type '",
                        fields[j].get_access(maps[k]),"'"})
                        return;
                    end
                end
            end
        end

        // Access each register:
        // - Write complement of reset value via front door
        // - Read value via backdoor and compare against mirror
        // - Write reset value via backdoor
        // - Read via front door and compare against mirror
        foreach (maps[j]) begin
            uvm_status_e status;
            uvm_reg_data_t  v, exp;

            `uvm_info("reg_access_seq", {"Verifying access of register '",
                rg.get_full_name(),"' in map '", maps[j].get_full_name(),
            "' ..."}, UVM_LOW)

            v = rg.get();

            rg.write(status, ~v, UVM_FRONTDOOR, maps[j], this);

            if (status != UVM_IS_OK) begin
                `uvm_error("reg_access_seq", {"Status was '",status.name(),
                    "' when writing '",rg.get_full_name(),
                "' through map '",maps[j].get_full_name(),"'"})
            end
            #1;

            rg.mirror(status, UVM_CHECK, UVM_BACKDOOR, uvm_reg_map::backdoor(), this);
            if (status != UVM_IS_OK) begin
                `uvm_error("reg_access_seq", {"Status was '",status.name(),
                    "' when reading reset value of register '",
                rg.get_full_name(), "' through backdoor"})
            end

            rg.write(status, v, UVM_BACKDOOR, maps[j], this);
            if (status != UVM_IS_OK) begin
                `uvm_error("reg_access_seq", {"Status was '",status.name(),
                    "' when writing '",rg.get_full_name(),
                "' through backdoor"})
            end

            rg.mirror(status, UVM_CHECK, UVM_FRONTDOOR, maps[j], this);
            if (status != UVM_IS_OK) begin
                `uvm_error("reg_access_seq", {"Status was '",status.name(),
                    "' when reading reset value of register '",
                    rg.get_full_name(), "' through map '",
                maps[j].get_full_name(),"'"})
            end
        end
    endtask: body
endclass: reg_single_access_seq

//------------------------------------------------------------------------------
//
// Class: reg_access_seq
//
// Verify the accessibility of all registers in a block
// by executing the <reg_single_access_seq> sequence on
// every register within it.
//
// If bit-type resource named
// "NO_REG_TESTS" or "NO_REG_ACCESS_TEST"
// in the "REG::" namespace
// matches the full name of the block,
// the block is not tested.
//
//| uvm_resource_db#(bit)::set({"REG::",regmodel.blk.get_full_name(),".*"},
//|                            "NO_REG_TESTS", 1, this);
//
//------------------------------------------------------------------------------

class reg_access_seq extends uvm_reg_sequence #(uvm_sequence #(uvm_reg_item));

    // Variable: model
    //
    // The block to be tested. Declared in the base class.
    //
    //| uvm_reg_block model;

    // Variable: reg_seq
    //
    // The sequence used to test one register
    //
    protected reg_single_access_seq reg_seq;

    `uvm_object_utils(reg_access_seq)

    function new(string name="reg_access_seq");
        super.new(name);
    endfunction

    // Task: body
    //
    // Executes the Register Access sequence.
    // Do not call directly. Use seq.start() instead.
    //
    virtual task body();

        if (model == null) begin
            `uvm_error("reg_access_seq", "No register model specified to run sequence on")
            return;
        end

    uvm_report_info("STARTING_SEQ",{"\n\nStarting ",get_name()," sequence...\n"},UVM_LOW);

    reg_seq = reg_single_access_seq::type_id::create("single_reg_access_seq");

    this.reset_blk(model);
    model.reset();

    do_block(model);
endtask: body

// Task: do_block
//
// Test all of the registers in a block
//
protected virtual task do_block(uvm_reg_block blk);
    uvm_reg regs[$];

    if (uvm_resource_db#(bit)::get_by_name({"REG::",blk.get_full_name()},
    "NO_REG_TESTS", 0) != null ||
    uvm_resource_db#(bit)::get_by_name({"REG::",blk.get_full_name()},
    "NO_REG_ACCESS_TEST", 0) != null )
    return;

    // Iterate over all registers, checking accesses
    blk.get_registers(regs, UVM_NO_HIER);
    foreach (regs[i]) begin
        // Registers with some attributes are not to be tested
        if (uvm_resource_db#(bit)::get_by_name({"REG::",regs[i].get_full_name()},
        "NO_REG_TESTS", 0) != null ||
        uvm_resource_db#(bit)::get_by_name({"REG::",regs[i].get_full_name()},
        "NO_REG_ACCESS_TEST", 0) != null )
        continue;

        // Can only deal with registers with backdoor access
        if (regs[i].get_backdoor() == null && !regs[i].has_hdl_path()) begin
            `uvm_warning("reg_access_seq", {"Register '",regs[i].get_full_name(),
            "' does not have a backdoor mechanism available"})
            continue;
        end

        reg_seq.rg = regs[i];
        reg_seq.start(null,this);
    end

    begin
        uvm_reg_block blks[$];

        blk.get_blocks(blks);
        foreach (blks[i]) begin
            do_block(blks[i]);
        end
    end
endtask: do_block

// Task: reset_blk
//
// Reset the DUT that corresponds to the specified block abstraction class.
//
// Currently empty.
// Will rollback the environment's phase to the ~reset~
// phase once the new phasing is available.
//
// In the meantime, the DUT should be reset before executing this
// test sequence or this method should be implemented
// in an extension to reset the DUT.
//
virtual task reset_blk(uvm_reg_block blk);
endtask

endclass: reg_access_seq

class wddr_reg_access_seq extends wddr_base_seq;

    `uvm_object_utils(wddr_reg_access_seq)

    uvm_reg      regs[$];
    uvm_reg      temp_reg;

    reg_access_seq reg_seq;

    function new(string name="wddr_reg_access_seq");
        super.new(name);
    endfunction

    virtual task body();
        super.body();

        reg_seq       = reg_access_seq::type_id::create("reg_seq");
        reg_seq.model = this.reg_model;

        reg_model.get_registers(regs);

        foreach(regs[i]) begin
            temp_reg = regs[i];
            if(temp_reg.get_rights() == "RO" ) begin
            `uvm_info("RO REG", $sformatf("RO Registers Masked : %s",regs[i].get_name()),UVM_LOW)
            uvm_resource_db#(bit)::set({"REG::",temp_reg.get_full_name()},"NO_REG_TESTS", 1, this);
            end
        end
        reg_model.reset("HARD");

        reg_seq.start(null,this);

        #10000;

        `uvm_info(get_type_name(), $sformatf("REG ACCESS TEST Completed !!!!!!!"),UVM_LOW)

    endtask : body

endclass
