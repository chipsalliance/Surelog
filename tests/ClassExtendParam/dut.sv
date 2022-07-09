package uvm;

virtual class uvm_sequence #(type REQ = uvm_sequence_item,
                             type RSP = REQ) extends uvm_sequence_base;
endclass

class uvm_reg_sequence #(type BASE=uvm_sequence #(uvm_reg_item)) extends BASE;
virtual task body();
begin 
   uvm_report_warning (m_sequencer.get_full_name()); 
end
endtask
endclass

virtual class uvm_component;
extern virtual function string get_full_name ();
endclass

class uvm_sequencer_base extends uvm_component;
endclass

virtual class uvm_sequence_base extends uvm_sequence_item;
endclass

class uvm_sequence_item;
protected  uvm_sequencer_base m_sequencer;
protected  uvm_sequence_base  m_parent_sequence;
function string get_full_name();
endfunction

endclass

endpackage
