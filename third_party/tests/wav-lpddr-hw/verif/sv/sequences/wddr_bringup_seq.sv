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
class wddr_bringup_seq extends wddr_base_seq;

    function new(string name="wddr_bringup_seq");
        super.new(name);
    endfunction

    `uvm_object_utils(wddr_bringup_seq)

    virtual task body();
        super.body();

        phy_bringup;

        `uvm_info(get_type_name(), $sformatf("DFI sequence completed!!!!!!!!"),UVM_LOW)

    endtask : body
endclass

class wddr_dfi_freqsw_seq extends wddr_base_seq;

    function new(string name="wddr_dfi_freqsw_seq");
        super.new(name);
    endfunction

    `uvm_object_utils(wddr_dfi_freqsw_seq)

    virtual task body();
        super.body();

        dfi_freqsw;

        `uvm_info(get_type_name(), $sformatf("wddr_dfi_freqsw_seq sequence completed!!!!!!!!"),UVM_LOW)

    endtask : body
endclass

class wddr_mcu_freqsw_seq extends wddr_base_seq;

    function new(string name="wddr_mcu_freqsw_seq");
        super.new(name);
    endfunction

    `uvm_object_utils(wddr_mcu_freqsw_seq)

    virtual task body();
        super.body();

        config_vips(vcoFreq1,freqRatio);
        mcu_freqsw;

        `uvm_info(get_type_name(), $sformatf("wddr_mcu_freqsw_seq sequence completed!!!!!!!!"),UVM_LOW)

    endtask : body
endclass

class wddr_mcu_dfiupdate_seq extends wddr_base_seq;

    function new(string name="wddr_mcu_dfiupdate_seq");
        super.new(name);
    endfunction

    `uvm_object_utils(wddr_mcu_dfiupdate_seq)

    virtual task body();
        super.body();

        config_vips(vcoFreq1,freqRatio);
        mcu_dfiupdate;

        `uvm_info(get_type_name(), $sformatf("wddr_mcu_dfiupdate_seq sequence completed!!!!!!!!"),UVM_LOW)

    endtask : body
endclass

class wddr_mcu_dfiphymas_seq extends wddr_base_seq;

    function new(string name="wddr_mcu_dfiphymas_seq");
        super.new(name);
    endfunction

    `uvm_object_utils(wddr_mcu_dfiphymas_seq)

    virtual task body();
        super.body();

        config_vips(vcoFreq1,freqRatio);
        mcu_dfiphymas;

        `uvm_info(get_type_name(), $sformatf("wddr_mcu_dfiphymas_seq sequence completed!!!!!!!!"),UVM_LOW)

    endtask : body
endclass

class wddr_mcu_dfilp_seq extends wddr_base_seq;

    function new(string name="wddr_mcu_dfilp_seq");
        super.new(name);
    endfunction

    `uvm_object_utils(wddr_mcu_dfilp_seq)

    virtual task body();
        super.body();

        config_vips(vcoFreq1,freqRatio);
        mcu_dfilp;

        `uvm_info(get_type_name(), $sformatf("wddr_mcu_dfilp_seq sequence completed!!!!!!!!"),UVM_LOW)

    endtask : body
endclass
