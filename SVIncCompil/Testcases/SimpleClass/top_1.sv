
program class_t;

  // Class with constructor, with no parameter

  class A;
     integer size;
     integer size2;

     // Constructor
     function new ();
       begin
         this.size = 0;
       end 
     endfunction
  
   endclass
 

  class Register1 #(parameter int N = 1);
    bit [N-1:0] data;
    bit [N-1:0] data;

    virtual function void print_tree1();
		string nice_string = "";
    endfunction

    virtual function void print_tree2();
		string nice_string = "";
    endfunction

  endclass

 


 class Register2 #(parameter int N = 1);
    bit [N-1:0] data;
  endclass

class Register2 #(parameter int N = 1);
    bit [N-1:0] data;
  endclass


class Register2 #(parameter int N = 1);
    bit [N-1:0] data;
 


function new(string port_name, string lookup_name="", uvm_packer packer=null);

   
    
 //       `uvm_fatal("UVMC",{"Port '",exist_port.m_port_name,
 //                  "' is already bound to '", bound_port.get_full_name(),"'"})
        
    

  endfunction

 endclass


endprogram
