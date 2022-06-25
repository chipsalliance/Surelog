package pkg;

  class uvm_object;
  endclass
   
  class uvm_callback;
   int get_inst_id;
  endclass

class uvm_callbacks #(type T=uvm_object, type CB=uvm_callback);

 function void get_all (  );
  
  CB cb;
  CB callbacks_to_append[$];
  CB unique_callbacks_to_append[$];

  // Now remove duplicates and append the final list to all_callbacks.
  unique_callbacks_to_append = callbacks_to_append.unique( cb_ ) with ( cb_.get_inst_id );
  
endfunction

endclass

endpackage

module top();

pkg::uvm_callbacks c1;

endmodule // top
