////////////////////////////////////////////////
////s~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~s////
////s           www.testbench.in           s////
////s                                      s////
////s              UVM Tutorial            s////
////s                                      s////
////s            gopi@testbench.in          s////
////s~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~s////
//////////////////////////////////////////////// 
`ifndef GUARD_CONFIGURATION
`define GUARD_CONFIGURATION


class Configuration extends uvm_object;

    virtual input_interface.IP   input_intf;
    virtual mem_interface.MEM  mem_intf;
    virtual output_interface.OP output_intf[4];

    bit [7:0] device_add[4];

    virtual function uvm_object create(string name="");
        Configuration t = new();

        t.device_add = this.device_add;
        t.input_intf  =   this.input_intf;
        t.mem_intf    =   this.mem_intf;
        t.output_intf =   this.output_intf;

        return t;
    endfunction : create

endclass : Configuration

`endif
