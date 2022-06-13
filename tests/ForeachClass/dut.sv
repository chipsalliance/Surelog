package uvm;
  
  class uvm_reg_map;
    local logic m_mems_by_offset[10];
  endclass


  function f1();
    uvm_reg_map top_map;

    foreach (top_map.m_mems_by_offset[range]) begin
      if (addrs[i] >= range.min && addrs[i] <= range.max) begin
      end
    end
  endfunction

endpackage
