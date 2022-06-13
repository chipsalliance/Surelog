package uvm;
  
class uvm_phase;
  bit  m_predecessors[uvm_phase];
endclass


  function void uvm_phase::get_adjacent_predecessor_nodes();

  
     bit predecessors[uvm_phase];
  
     foreach (predecessors[p]) begin
           foreach (p.m_predecessors[next_p]) begin
             predecessors[next_p] = 1;
           end
     end
  

  endfunction 


endpackage
