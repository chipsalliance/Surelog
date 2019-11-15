////////////////////////////////////////////////
////s~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~s////
////s           www.testbench.in           s////
////s                                      s////
////s              UVM Tutorial            s////
////s                                      s////
////s            gopi@testbench.in          s////
////s~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~s////
//////////////////////////////////////////////// 
`ifndef GUARD_RECEIVER
`define GUARD_RECEIVER

class Receiver extends uvm_component;

    virtual output_interface.OP output_intf;

    Configuration cfg;

    integer id;

    uvm_analysis_port #(Packet) Rcvr2Sb_port;

   `uvm_component_utils(Receiver) 

    function new (string name, uvm_component parent);
        super.new(name, parent);
    endfunction : new


    virtual function void build();
        super.build();
        Rcvr2Sb_port = new("Rcvr2Sb", this);
    endfunction : build

    virtual function void end_of_elaboration();
        uvm_object tmp;
        super.end_of_elaboration();
        assert(get_config_object("Configuration",tmp));
        $cast(cfg,tmp);
        output_intf = cfg.output_intf[id]; 
    endfunction : end_of_elaboration

    virtual task run();
    Packet pkt;
         fork
         forever
         begin
            // declare the queue and dynamic array here 
	    // so they are automatically allocated for every packet
             bit [7:0] bq[$],bytes[];

             repeat(2) @(posedge output_intf.clock);
             wait(output_intf.cb.ready)
             output_intf.cb.read <= 1;  
    
             repeat(2) @(posedge output_intf.clock);
             while (output_intf.cb.ready)
             begin
                  bq.push_back(output_intf.cb.data_out);
                  @(posedge output_intf.clock);
             end
             bytes = new[bq.size()] (bq); // Copy queue into dyn array

             output_intf.cb.read <= 0;   
             @(posedge output_intf.clock);
             uvm_report_info(get_full_name(),"Received packet ...",UVM_LOW);
             pkt = new();
             void'(pkt.unpack_bytes(bytes));
             Rcvr2Sb_port.write(pkt);
         end
         join

     endtask : run


endclass :  Receiver

`endif

