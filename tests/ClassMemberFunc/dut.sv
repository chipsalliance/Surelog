package pkg;

class uvm_queue;
endclass

class uvm_resource_types;

  typedef uvm_queue#(uvm_resource_base) rsrc_q_t;

endclass

function void uvm_sequencer_base::start_phase_sequence();
uvm_resource_types::rsrc_q_t rq;
//for (int i = 0; seq == null && i < rq.size(); i++) begin
  uvm_resource_base rsrc = rq.get(i);
//end

endfunction

endpackage

