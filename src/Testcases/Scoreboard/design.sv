import uvm_pkg::*;
`include "uvm_macros.svh"
  
// Simple scoreboard.
// When receiving transaction on analysis port,
// it is added to internal_state.
class my_scoreboard extends uvm_scoreboard;

  uvm_analysis_imp #(int, my_scoreboard) m_imp;
  int internal_state;
  
  `uvm_component_utils(my_scoreboard)

  function new (string name, uvm_component parent);
    super.new(name, parent);
    m_imp = new("imp", this);
  endfunction
  
  function write (int pkt);
    `uvm_info("write", "Write to analysis port", UVM_HIGH)
    internal_state += pkt;
  endfunction

endclass