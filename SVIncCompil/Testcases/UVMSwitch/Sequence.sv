////////////////////////////////////////////////
////s~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~s////
////s           www.testbench.in           s////
////s                                      s////
////s              UVM Tutorial            s////
////s                                      s////
////s            gopi@testbench.in          s////
////s~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~s////
//////////////////////////////////////////////// 

class Seq_device0_and_device1 extends uvm_sequence #(Packet);

     function new(string name = "Seq_device0_and_device1");
         super.new(name);
     endfunction : new
 
     Packet item;
 
     `uvm_sequence_utils(Seq_device0_and_device1, Sequencer)    

     virtual task body();
        forever begin
         `uvm_do_with(item, {da == p_sequencer.cfg.device_add[0];} ); 
         `uvm_do_with(item, {da == p_sequencer.cfg.device_add[1];} ); 
        end
     endtask : body
  
endclass : Seq_device0_and_device1

class Seq_constant_length extends uvm_sequence #(Packet);

     function new(string name = "Seq_constant_length");
         super.new(name);
     endfunction : new
 
     Packet item;
 
     `uvm_sequence_utils(Seq_constant_length, Sequencer)    

     virtual task body();
        forever begin
         `uvm_do_with(item, {length == 10; da == p_sequencer.cfg.device_add[0];} ); 
        end
     endtask : body
  
endclass : Seq_constant_length

