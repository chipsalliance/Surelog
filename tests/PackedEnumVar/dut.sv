module top;
   typedef enum logic [2:0] {
      A = 3'b000,
      B = 3'b111
   } sp2v_e;


   int          o;
   function automatic sp2v_e [1:0] get_BA();
      sp2v_e [1:0] out;
      out[0] = B;
      return out;
   endfunction
   
   assign o = int'(get_BA());

   
endmodule
