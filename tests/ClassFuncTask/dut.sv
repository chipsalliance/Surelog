package pack;

class C #(type T=int);
  int x;

  function new (int bound = 0);
   super.new (name, parent, UVM_PORT, min_size, max_size);
  endfunction
   
  task set (int i);
    x = i;
  endtask
  function int get;
    return x;
  endfunction
endclass

endpackage
