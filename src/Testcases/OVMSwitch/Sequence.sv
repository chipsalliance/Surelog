////////////////////////////////////////////////
////s~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~s////
////s           www.testbench.in           s////
////s                                      s////
////s              OVM Tutorial            s////
////s                                      s////
////s            gopi@testbench.in          s////
////s~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~s////
//////////////////////////////////////////////// 

class Seq_device0_and_device1 extends ovm_sequence #(Packet);

     function new(string name = "Seq_device0_and_device1");
         super.new(name);
     endfunction : new
 
     Packet item;
 
     `ovm_sequence_utils(Seq_device0_and_device1, Sequencer)    

     virtual task body();
        forever begin
         `ovm_do_with(item, {da == p_sequencer.cfg.device0_add;} ); 
         `ovm_do_with(item, {da == p_sequencer.cfg.device1_add;} ); 
        end
     endtask : body
  
endclass : Seq_device0_and_device1

class Seq_constant_length extends ovm_sequence #(Packet);

     function new(string name = "Seq_constant_length");
         super.new(name);
     endfunction : new
 
     Packet item;
 
     `ovm_sequence_utils(Seq_constant_length, Sequencer)    

     virtual task body();
        forever begin
         `ovm_do_with(item, {length == 10; da == p_sequencer.cfg.device0_add;} ); 
        end
     endtask : body
  
endclass : Seq_constant_length

