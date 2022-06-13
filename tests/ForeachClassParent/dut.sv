package uvm;
  
class root;
  protected uvm_phase m_type_overrides[$];
endclass

class uvm_phase extends root;
endclass

  function void uvm_phase::get_adjacent_predecessor_nodes();
    
     foreach (m_type_overrides[index]) begin
     end

  endfunction 


endpackage
