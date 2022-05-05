package pkg;

class uvm_tlm_fifo;

 bit print_enabled = 1;

endclass
   
class uvm_sequencer_analysis_fifo #(type RSP = uvm_sequence_item) extends uvm_tlm_fifo #(RSP);
endclass

class uvm_sequencer_param_base #(type REQ = uvm_sequence_item,
                                 type RSP = REQ) extends uvm_sequencer_base;

  uvm_sequencer_analysis_fifo #(RSP) sqr_rsp_analysis_fifo;
endclass


function uvm_sequencer_param_base::new ();
  
  sqr_rsp_analysis_fifo.print_enabled = 0;
 
endfunction


endpackage
