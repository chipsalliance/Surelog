package uvm;

class uvm_object;
protected bit  m_successors[uvm_phase];
endclass


class uvm_barrier extends uvm_object;

  local  int       threshold;
  
  function new ();
    this.threshold = threshold;
   
  endfunction

endclass

class uvm_phase extends uvm_object;
protected bit  m_predecessors[uvm_phase];
extern function void add();
endclass

function void uvm_phase::add();
                        
                         
    this.m_predecessors.size = super.m_successors;
                      
                               
endfunction                        


endpackage;
