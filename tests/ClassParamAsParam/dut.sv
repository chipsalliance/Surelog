virtual class object#(type T=int);
endclass

class resource #(type T=int);
endclass

class resource_db #(type T=int);

 typedef resource #(T) rsrc_t;
 rsrc_t rsrc;
 
endclass

class config_db#(type T=int) extends resource_db#(T);
endclass

module top ();
  config_db#(object#(longint)) misc2 = new;
endmodule
