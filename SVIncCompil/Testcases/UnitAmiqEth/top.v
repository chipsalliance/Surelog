

package all_c;
  class E;
  endclass

 class D extends E;
 endclass


class uvm_blocking_get_export #(type T=int)
  extends uvm_port_base #(uvm_tlm_if_base #(T,T));
endclass 

class uvm_component;
endclass


virtual class uvm_port_base #(type IF=uvm_void) extends IF;
endclass   


endpackage

import all_c::*;

module top ();
   class C;
   endclass

   class A extends C;  
   endclass

   class B extends D;  
   endclass

endmodule
