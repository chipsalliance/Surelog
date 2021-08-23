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
`ifndef WDDR_DT_FREQSW_TEST
`define WDDR_DT_FREQSW_TEST

class wddr_dt_freqsw_test extends wddr_base_test;

    `uvm_component_utils(wddr_dt_freqsw_test)

    function new(string name = "wddr_dt_freqsw_test", uvm_component parent=null);
        super.new(name,parent);
    endfunction : new

    virtual function void build_phase(uvm_phase phase);
        super.build_phase(phase);
    endfunction : build_phase

    function void end_of_elaboration_phase(uvm_phase phase);
        super.end_of_elaboration_phase(phase);
    endfunction

    function void connect_phase(uvm_phase phase);
        super.connect_phase(phase);
    endfunction

    task run_phase(uvm_phase phase);

        uvm_objection objection;

        wddr_dt_freqsw_seq  freq_sw_seq;

        `uvm_info(get_type_name(),$psprintf("------- Running seq Freq SW TEST ---------"), UVM_LOW)

        phase.raise_objection(this, "start_test");

        super.run_phase(phase);

        freq_sw_seq  = wddr_dt_freqsw_seq::type_id::create("freq_sw_seq");

        freq_sw_seq.start(null);

        phase.drop_objection(this,"Done test.");

    endtask

endclass

`endif
