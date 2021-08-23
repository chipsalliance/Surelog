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
class reg_single_reg_bitbash_seq extends uvm_reg_sequence #(uvm_sequence #(uvm_reg_item));

    // Variable: rg
    // The register to be tested
    uvm_reg rg;

    `uvm_object_utils(reg_single_reg_bitbash_seq)

    function new(string name="reg_single_reg_bitbash_seq");
        super.new(name);
    endfunction

    virtual task body();
        uvm_reg_field fields[$];
        string mode[`UVM_REG_DATA_WIDTH];
        uvm_reg_map maps[$];
        uvm_reg_data_t  dc_mask;
        uvm_reg_data_t  reset_val;
        int n_bits;
        int VALUE_NO_REG_TESTS;

        if (rg == null) begin
            `uvm_error("reg_bitbash_seq", "No register specified to run sequence on");
            return;
        end

        uvm_resource_db#(bit)::read_by_name({"REG::",rg.get_full_name()},"NO_REG_TESTS", VALUE_NO_REG_TESTS, null);

            if ( VALUE_NO_REG_TESTS  == 1 ) begin
                VALUE_NO_REG_TESTS = 0;
                return;
            end

            // Registers with some attributes are not to be tested
            if (uvm_resource_db#(bit)::get_by_name({"REG::",rg.get_full_name()},
            "NO_REG_TESTS", 0) != null ||
            uvm_resource_db#(bit)::get_by_name({"REG::",rg.get_full_name()},
            "NO_REG_BIT_BASH_TEST", 0) != null )
            return;

            n_bits = rg.get_n_bytes() * 8;

            // Let's see what kind of bits we have...
            rg.get_fields(fields);

            // Registers may be accessible from multiple physical interfaces (maps)
            rg.get_maps(maps);

            // Bash the bits in the register via each map
            foreach (maps[j]) begin
                uvm_status_e status;
                uvm_reg_data_t  val, exp, v;
                int next_lsb;

                next_lsb = 0;
                dc_mask  = 0;
                foreach (fields[k]) begin
                    int lsb, w, dc;

                    dc = (fields[k].get_compare() == UVM_NO_CHECK);
                    lsb = fields[k].get_lsb_pos();
                    w   = fields[k].get_n_bits();
                    // Ignore Write-only fields because
                    // you are not supposed to read them
                    case (fields[k].get_access(maps[j]))
                        "WO", "WOC", "WOS", "WO1": dc = 1;
                    endcase
                    // Any unused bits on the right side of the LSB?
                    while (next_lsb < lsb) mode[next_lsb++] = "RO";

                    repeat (w) begin
                        mode[next_lsb] = fields[k].get_access(maps[j]);
                        dc_mask[next_lsb] = dc;
                        next_lsb++;
                    end
                end
                // Any unused bits on the left side of the MSB?
                while (next_lsb < `UVM_REG_DATA_WIDTH)
                    mode[next_lsb++] = "RO";

                `uvm_info("reg_bitbash_seq", $sformatf("Verifying bits in register %s in map \"%s\"...",
                rg.get_full_name(), maps[j].get_full_name()),UVM_LOW);

                // Bash the kth bit
                for (int k = 0; k < n_bits; k++) begin
                    // Cannot test unpredictable bit behavior
                    if (dc_mask[k]) continue;

                    bash_kth_bit(rg, k, mode[k], maps[j], dc_mask);
                end

            end
        endtask: body

        task bash_kth_bit(uvm_reg         rg,
                int             k,
                string          mode,
                uvm_reg_map     map,
            uvm_reg_data_t  dc_mask);
            uvm_status_e status;
            uvm_reg_data_t  val, exp, v;
            bit bit_val;

        `uvm_info("reg_bitbash_seq", $sformatf("...Bashing %s bit #%0d", mode, k),UVM_HIGH);

        repeat (2) begin
            val = rg.get();
            v   = val;
            exp = val;
            val[k] = ~val[k];
            bit_val = val[k];

            rg.write(status, val, UVM_FRONTDOOR, map, this);
            if (status != UVM_IS_OK) begin
                `uvm_error("reg_bitbash_seq", $sformatf("Status was %s when writing to register \"%s\" through map \"%s\".",
                status.name(), rg.get_full_name(), map.get_full_name()));
            end

            exp = rg.get() & ~dc_mask;
            rg.read(status, val, UVM_FRONTDOOR, map, this);
            if (status != UVM_IS_OK) begin
                `uvm_error("reg_bitbash_seq", $sformatf("Status was %s when reading register \"%s\" through map \"%s\".",
                status.name(), rg.get_full_name(), map.get_full_name()));
            end

            val &= ~dc_mask;
            if (val !== exp) begin
                `uvm_error("reg_bitbash_seq", $sformatf("Writing a %b in bit #%0d of register \"%s\" with initial value 'h%h yielded 'h%h instead of 'h%h",
                bit_val, k, rg.get_full_name(), v, val, exp));
            end
        end
    endtask: bash_kth_bit

endclass: reg_single_reg_bitbash_seq

class reg_bitbash_seq extends uvm_reg_sequence #(uvm_sequence #(uvm_reg_item));

    // Variable: model
    //
    // The block to be tested. Declared in the base class.
    //
    //| uvm_reg_block model;

    // Variable: reg_seq
    //
    // The sequence used to test one register
    //
    protected reg_single_reg_bitbash_seq reg_seq;

    `uvm_object_utils(reg_bitbash_seq)

    function new(string name="reg_bitbash_seq");
        super.new(name);
    endfunction

    // Task: body
    //
    // Executes the Register Bit Bash sequence.
    // Do not call directly. Use seq.start() instead.
    //
    virtual task body();

        if (model == null) begin
            `uvm_error("reg_bitbash_seq", "No register model specified to run sequence on");
            return;
        end

    uvm_report_info("STARTING_SEQ",{"\n\nStarting ",get_name()," sequence...\n"},UVM_LOW);

    reg_seq = reg_single_reg_bitbash_seq::type_id::create("reg_single_bit_bash_seq");

    this.reset_blk(model);
    model.reset();

    do_block(model);
endtask

// Task: do_block
//
// Test all of the registers in a a given ~block~
//
protected virtual task do_block(uvm_reg_block blk);
    uvm_reg regs[$];
    int VALUE_NO_REG_TESTS;

    // Iterate over all registers, checking accesses
    blk.get_registers(regs, UVM_NO_HIER);
    foreach (regs[i]) begin

        // Registers with some attributes are not to be tested
        uvm_resource_db#(bit)::read_by_name({"REG::",regs[i].get_full_name()},"NO_REG_TESTS", VALUE_NO_REG_TESTS, null);

            `uvm_info(get_type_name(), $sformatf("REGISTER %s NO_REG_TESTS=%d", regs[i].get_full_name(),VALUE_NO_REG_TESTS), UVM_LOW);

            if ( VALUE_NO_REG_TESTS  == 1 ) begin
                VALUE_NO_REG_TESTS = 0;
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

            `uvm_info("reg_bitbash_seq", $sformatf("Get next block %d",i),UVM_HIGH);

        end

    `uvm_info("reg_bitbash_seq", $sformatf("Done all blocks"),UVM_HIGH);

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

endclass: reg_bitbash_seq

class wddr_reg_bitbash_seq extends wddr_base_seq;

    `uvm_object_utils(wddr_reg_bitbash_seq)
    uvm_reg      regs[$];
    uvm_reg      temp_reg;

    reg_bitbash_seq reg_seq;

    function new(string name="wddr_reg_bitbash_seq");
        super.new(name);
    endfunction

    virtual task body();
        super.body();

        reg_seq       = reg_bitbash_seq::type_id::create("reg_seq");
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

        #100ns;

        `uvm_info(get_type_name(), $sformatf("REG RESET TEST Completed !!!!!!!"),UVM_LOW)

    endtask : body

endclass
