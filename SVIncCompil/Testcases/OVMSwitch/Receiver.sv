////////////////////////////////////////////////
////s~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~s////
////s           www.testbench.in           s////
////s                                      s////
////s              OVM Tutorial            s////
////s                                      s////
////s            gopi@testbench.in          s////
////s~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~s////
//////////////////////////////////////////////// 
`ifndef GUARD_RECEIVER
`define GUARD_RECEIVER

class Receiver extends ovm_component;

    virtual output_interface.OP output_intf;

    Configuration cfg;

    integer id;

    ovm_analysis_port #(Packet) Rcvr2Sb_port;

   `ovm_component_utils(Receiver) 

    function new (string name, ovm_component parent);
        super.new(name, parent);
    endfunction : new


    function void build();
        super.build();
        Rcvr2Sb_port = new("Rcvr2Sb", this);
    endfunction : build

    function void end_of_elaboration();
        ovm_object tmp;
        super.end_of_elaboration();
        assert(get_config_object("Configuration",tmp));
        $cast(cfg,tmp);
        output_intf = cfg.output_intf[id]; 
    endfunction : end_of_elaboration

     virtual task run();
     bit [7:0] bytes[];
     Packet pkt;

         fork
         forever
         begin
             repeat(2) @(posedge output_intf.clock);
             wait(output_intf.cb.ready)
             output_intf.cb.read <= 1;  
    
             repeat(2) @(posedge output_intf.clock);
             while (output_intf.cb.ready)
             begin
                   bytes = new[bytes.size + 1](bytes);
                   bytes[bytes.size - 1] = output_intf.cb.data_out;
                  @(posedge output_intf.clock);
             end

             output_intf.cb.read <= 0;   
             @(posedge output_intf.clock);
             ovm_report_info(get_full_name(),"Received packet ...",OVM_LOW);
             pkt = new();
             pkt.unpack_bytes(bytes);
             Rcvr2Sb_port.write(pkt);
             bytes.delete();   
         end
         join

     endtask : run


endclass :  Receiver

`endif

