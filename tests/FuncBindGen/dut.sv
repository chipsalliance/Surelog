module top(output int o);
   parameter  int unsigned Depth  = 500;
   localparam int unsigned PTR_WIDTH = 3;

   if (Depth > 2) begin : gen_block
      function automatic [PTR_WIDTH-1:0] get_casted_param();
         logic [PTR_WIDTH-1:0] dec_tmp_sub = (PTR_WIDTH)'(Depth);
         return dec_tmp_sub;
      endfunction

      assign o = int'(get_casted_param());
   end

endmodule
