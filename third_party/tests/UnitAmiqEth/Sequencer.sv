////////////////////////////////////////////////
////s~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~s////
////s           www.testbench.in           s////
////s                                      s////
////s              UVM Tutorial            s////
////s                                      s////
////s            gopi@testbench.in          s////
////s~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~s////
//////////////////////////////////////////////// 
`ifndef GUARD_SEQUENCER
`define GUARD_SEQUENCER

class Sequencer extends uvm_sequencer #(Packet);

     Configuration cfg;
   
    `uvm_sequencer_utils(Sequencer)
  
    function new (string name, uvm_component parent);
        super.new(name, parent);
        `uvm_update_sequence_lib_and_item(Packet)
    endfunction : new
  
  
    virtual function void end_of_elaboration();
        uvm_object tmp;
        assert(get_config_object("Configuration",tmp));
        $cast(cfg,tmp);
    endfunction

endclass : Sequencer

`endif

