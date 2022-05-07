module mod ();

  generate
    if (1) begin : cscope
      function automatic logic local_function(input  x);
        local_function = x + 1;
      endfunction
    end
  endgenerate
  
  assign foo = cscope.local_function(counter);
endmodule

module top ();
  mod  c ();
endmodule
