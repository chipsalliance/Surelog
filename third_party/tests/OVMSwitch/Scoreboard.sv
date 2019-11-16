////////////////////////////////////////////////
////s~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~s////
////s           www.testbench.in           s////
////s                                      s////
////s              OVM Tutorial            s////
////s                                      s////
////s            gopi@testbench.in          s////
////s~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~s////
//////////////////////////////////////////////// 
`ifndef GUARD_SCOREBOARD
`define GUARD_SCOREBOARD

`ovm_analysis_imp_decl(_rcvd_pkt)
`ovm_analysis_imp_decl(_sent_pkt)

class Scoreboard extends ovm_scoreboard;
    `ovm_component_utils(Scoreboard)
   
    Packet exp_que[$];
   
    ovm_analysis_imp_rcvd_pkt #(Packet,Scoreboard) Rcvr2Sb_port;
    ovm_analysis_imp_sent_pkt #(Packet,Scoreboard) Drvr2Sb_port;
   
    function new(string name, ovm_component parent);
        super.new(name, parent);
        Rcvr2Sb_port = new("Rcvr2Sb", this);
        Drvr2Sb_port = new("Drvr2Sb", this);
    endfunction : new
   
    virtual function void write_rcvd_pkt(input Packet pkt);
        Packet exp_pkt;
      //  pkt.print();

        if(exp_que.size())
        begin
           exp_pkt = exp_que.pop_front();
      //     exp_pkt.print();
           if( pkt.compare(exp_pkt))
             ovm_report_info(get_type_name(), $psprintf("Sent packet and reeived packet mathed"), OVM_LOW);
           else
             ovm_report_error(get_type_name(), $psprintf("Sent packet and reeived packet mismatched"), OVM_LOW);
        end
        else
             ovm_report_error(get_type_name(), $psprintf("No more packets to in the expected queue to compare"), OVM_LOW);
   endfunction : write_rcvd_pkt
   
   virtual function void write_sent_pkt(input Packet pkt);
        exp_que.push_back(pkt);
   endfunction : write_sent_pkt
   
   
   virtual function void report();
        ovm_report_info(get_type_name(),
        $psprintf("Scoreboard Report \n%s", this.sprint()), OVM_LOW);
   endfunction : report

  
endclass : Scoreboard

`endif
