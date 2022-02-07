package b;
  typedef struct packed {
    logic [10:0]         vc;
  } foo_bar_t;

endpackage 

package aa;

  function automatic b::foo_bar_t foo_bar;

    input b::foo_bar_t a;

    b::foo_bar_t y;
    reg [$bits(a)-1:0] a_vec;

    begin
      foo_bar = y; // return the whole struct
    end

  endfunction
endpackage 
