module top(output int o);
   initial begin
      o = 0;
      {o[1:0]} = 2'b11;
   end

   assign   {o[1:0]} = 2'b11;
endmodule // top
