package uvm;
           

class uvm_vreg_field_cb_iter;
extern virtual function int first();
 
endclass

class uvm_vreg_field_cbs extends uvm_vreg_field_cb_iter;
  int fname;
endclass


class uvm_vreg ;
   extern  task write();
endclass

task uvm_vreg::write();
  uvm_vreg_field_cbs cbs;
  cbs.fname = cbs.first();
endtask

endpackage
