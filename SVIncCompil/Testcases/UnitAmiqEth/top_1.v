

package all_c;
 
class uvm_sequence_item;
endclass

virtual class uvm_sequencer #(type IF=uvm_void) extends IF;
endclass   


typedef uvm_sequencer #(uvm_sequence_item) uvm_virtual_sequencer;


class toto extends uvm_virtual_sequencer;
endclass

endpackage
