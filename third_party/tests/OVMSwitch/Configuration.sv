////////////////////////////////////////////////
////s~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~s////
////s           www.testbench.in           s////
////s                                      s////
////s              OVM Tutorial            s////
////s                                      s////
////s            gopi@testbench.in          s////
////s~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~s////
//////////////////////////////////////////////// 
`ifndef GUARD_CONFIGURATION
`define GUARD_CONFIGURATION


class Configuration extends ovm_object;

    virtual input_interface.IP   input_intf;
    virtual mem_interface.MEM  mem_intf;
    virtual output_interface.OP output_intf[4];

    bit [7:0] device0_add ;
    bit [7:0] device1_add ;
    bit [7:0] device2_add ;
    bit [7:0] device3_add ;

    virtual function ovm_object create(string name="");
        Configuration t = new();

        t.device0_add = this.device0_add;
        t.device1_add = this.device1_add;
        t.device2_add = this.device2_add;
        t.device3_add = this.device3_add;
        t.input_intf  =   this.input_intf;
        t.mem_intf    =   this.mem_intf;
        t.output_intf =   this.output_intf;

        return t;
    endfunction : create

endclass : Configuration

`endif
