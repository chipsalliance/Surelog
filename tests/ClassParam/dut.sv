package pack;

class uvm_port_base;
parameter p1 = 10;
localparam p2 = 5 * p1;

   class embedded;
     function new (int bound = 0);
     endfunction
   endclass
   
endclass   

endpackage
