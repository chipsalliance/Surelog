module top(output int o);
   typedef logic [4:0][1:0] box_t;

   assign o = int'(iota('1));
   
   function automatic logic [1:0] iota(box_t state);
      box_t result;
      result[0][1:0] = state[0][1:0];
      return result[0];
   endfunction : iota

endmodule


