////////////////////////////////////////////////
////s~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~s////
////s           www.testbench.in           s////
////s                                      s////
////s              OVM Tutorial            s////
////s                                      s////
////s            gopi@testbench.in          s////
////s~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~s////
//////////////////////////////////////////////// 
`ifndef GUARD_ENV
`define GUARD_ENV


class Environment extends ovm_env;

    `ovm_component_utils(Environment)

     Sequencer Seqncr;
     Driver Drvr;
     Receiver Rcvr[4];
     Scoreboard Sbd;
 
    function new(string name , ovm_component parent = null);
        super.new(name, parent);
    endfunction: new


    function void build();
        super.build();
        ovm_report_info(get_full_name(),"START of build ",OVM_LOW);

        Drvr   = Driver::type_id::create("Drvr",this);
        Seqncr = Sequencer::type_id::create("Seqncr",this);
        
        foreach(Rcvr[i]) begin
            Rcvr[i]   = Receiver::type_id::create($psprintf("Rcvr%0d",i),this);
            Rcvr[i].id = i;
        end

        Sbd   = Scoreboard::type_id::create("Sbd",this);
        
        ovm_report_info(get_full_name(),"END of build ",OVM_LOW);
    endfunction
    
    function void connect();
        super.connect();
        ovm_report_info(get_full_name(),"START of connect ",OVM_LOW);

        Drvr.seq_item_port.connect(Seqncr.seq_item_export);

        Drvr.Drvr2Sb_port.connect(Sbd.Drvr2Sb_port);

        Rcvr[0].Rcvr2Sb_port.connect(Sbd.Rcvr2Sb_port);
        Rcvr[1].Rcvr2Sb_port.connect(Sbd.Rcvr2Sb_port);
        Rcvr[2].Rcvr2Sb_port.connect(Sbd.Rcvr2Sb_port);
        Rcvr[3].Rcvr2Sb_port.connect(Sbd.Rcvr2Sb_port);

        ovm_report_info(get_full_name(),"END of connect ",OVM_LOW);
    endfunction


endclass : Environment

`endif 
