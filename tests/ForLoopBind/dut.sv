package uvm;
                
class  uvm_vreg_cb_iter;
endclass

class uvm_vreg_field_cb_iter;
  function int first();
  endfunction
  function int next();
  endfunction
endclass

class uvm_vreg_field_cbs;
  int fname;
endclass

class uvm_vreg_field;
endclass

class uvm_vreg ;
   local uvm_vreg_field fields[$]; 
   extern  task write();
endclass

task uvm_vreg::write();
   uvm_vreg_cb_iter cbs = new(this);
   foreach (fields[i]) begin
      uvm_vreg_field_cb_iter cbs = new(fields[i]);
      for (uvm_vreg_field_cbs cb = cbs; cb != null;
           cb = cbs) begin
         cb.fname = 1;        
      end
   end
endtask

endpackage // uvm
   
