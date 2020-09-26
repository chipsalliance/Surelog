package pack;

class Base;
endclass
   
virtual class uvm_port_base1 #(type IF=uvm_void) extends IF;
endclass   

class uvm_port_base2 #(type IF=uvm_void) extends Base;
endclass   

   
endpackage
