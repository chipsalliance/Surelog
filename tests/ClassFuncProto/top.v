
//import uvm_pkg::* ;
//`include "uvm_macros.svh"


module toto();

class c2 ;

typedef int this_type;

endclass


class c3 extends c2;
endclass

class c1 extends c3 ;
  

typedef enum bit [1:0]
{
  UVM_INFO,
  UVM_WARNING,
  UVM_ERROR = "toto",
  UVM_FATAL
} uvm_severity;


function REQ get_current_item();
    REQ t;
  
  endfunction

 function void connect(this_type provider);
endfunction

   function int get_verbosity_level(uvm_severity severity=UVM_ERROR,  uvm_reg reg_a[] );
   endfunction

 function int set_verbosity_level(uvm_severity severity=UVM_WARNING,  uvm_reg reg_a[] );
   endfunction

 task wait_for_total_count(c2 obj=null, int count=0);
    
  endtask
   
endclass

 DD d;

endmodule

