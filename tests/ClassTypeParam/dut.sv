virtual class uvm_object;
endclass

class uvm_resource #(type T=int);
endclass

class uvm_resource_db #(type T=int);

 typedef uvm_resource #(T) rsrc_t;
 rsrc_t rsrc;
 virtual function void check_all_sva_passed(string a_error_msg);
 endfunction
 
endclass

class uvm_config_db#(type T=int, type T2=int) extends uvm_resource_db#(T);
endclass


typedef uvm_config_db#(uvm_object, string) m_uvm_config_obj_misc;

module top ();

  m_uvm_config_obj_misc misc1 = new;

  uvm_config_db#(uvm_object, string) misc2 = new;
endmodule
