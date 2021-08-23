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

`ifndef WDDR_BASE_TEST
`define WDDR_BASE_TEST

class wddr_base_test extends uvm_test;

    `uvm_component_utils(wddr_base_test)

    uvm_table_printer printer;

    uvm_reg      regs[$];
    uvm_reg      temp_reg,temp_reg2;
    uvm_status_e status;

    string REG_PREFIX = "wddr";
    integer rc;

    bit [63:0] rval;
    string     reg_name;

    uvm_reg_field field;
    uvm_reg_field expected;

    wddr_tb tb;

    `ifdef DFIMC
        cdnDfimcUvmUserSve dfimcSve;
    `endif
    `ifdef LPDDR4
        cdnLpddr4UvmUserSve lpddr4Sve0;
    `endif

    //===========================================================================
    //Constructor
    //===========================================================================
    function new(string name = "wddr_base_test",
        uvm_component parent=null);
        super.new(name,parent);
    endfunction : new

    //===========================================================================
    //Build Phase
    //===========================================================================

    virtual function void build_phase(uvm_phase phase);
        super.build_phase(phase);

        tb = wddr_tb::type_id::create("tb", this);
        `ifdef DFIMC
            dfimcSve = cdnDfimcUvmUserSve::type_id::create("dfimcSve", this);
        `endif
        `ifdef LPDDR4
            lpddr4Sve0 = cdnLpddr4UvmUserSve::type_id::create("lpddr4Sve0", this);
        `endif

        // Enable transaction recording for everything
        uvm_config_db#(string)::set(uvm_root::get(), "*", "recording_detail", UVM_FULL);

        // Create a specific depth printer for printing the created topology
        printer = new();
        printer.knobs.depth = 4;

        uvm_config_db#(string)::set(uvm_root::get(), "*", "REG_PREFIX", REG_PREFIX);

    endfunction : build_phase

    //===========================================================================
    //Connect Phase
    //===========================================================================
    virtual function void connect_phase(uvm_phase phase);
        super.connect_phase(phase);

    endfunction : connect_phase

    //===========================================================================
    //Elaboration Phase
    //===========================================================================
    function void end_of_elaboration_phase(uvm_phase phase);
        `uvm_info(get_type_name(),$psprintf("Printing the test topology :\n%s", this.sprint(printer)), UVM_LOW)
    endfunction

    //===========================================================================
    //Start of Simulation Phase
    //===========================================================================
    function void start_of_simulation_phase(uvm_phase phase);
        super.start_of_simulation_phase(phase);
    endfunction // start_of_simulation_phase

    //===========================================================================
    //RUN Phase
    //===========================================================================
    task run_phase(uvm_phase phase);
        super.run_phase(phase);
        `ifndef NOT_USING_wddr_base_test
        tb.reg_model.get_registers(regs);

    `endif
        #1000ns;
    phase.phase_done.set_drain_time(this, 50);
endtask //run_phase

virtual function void report_phase( uvm_phase phase);
    uvm_report_server svr;
    svr =uvm_report_server ::get_server();

    if(svr.get_severity_count(UVM_FATAL) +  svr.get_severity_count(UVM_ERROR) >0)  begin
        uvm_report_info("REPORT_PHASE"," ***********************",UVM_LOW);
        uvm_report_info("REPORT_PHASE"," ***** TEST FAILED *****",UVM_LOW);
        uvm_report_info("REPORT_PHASE"," ***********************",UVM_LOW);
    end
    else  begin
        uvm_report_info("REPORT_PHASE"," ***********************",UVM_LOW);
        uvm_report_info("REPORT_PHASE"," ***** TEST PASSED *****",UVM_LOW);
        uvm_report_info("REPORT_PHASE"," ***********************",UVM_LOW);
    end
endfunction
endclass
`endif
