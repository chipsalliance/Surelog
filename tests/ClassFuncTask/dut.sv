package pack;

class C;
  int x;

  function new (int bound = 0);
  endfunction
   
  task set (int i);
    x = i;
  endtask
  function int get;
    return x;
  endfunction
endclass

endpackage
