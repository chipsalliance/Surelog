module top  (y, clk, sel);
   output wire y  ;
   input       clk;
   input       sel;
   reg         reg_assign = (1'h0) ;
   reg [1:0]   reg_count = (1'h0) ;
   assign y = reg_assign ;
   always @(posedge clk)
     if (sel)
       for (reg_count = 0; reg_count < 2; reg_count = reg_count + 1'h1)
         if (0);
         else reg_assign <= 1;
     else reg_assign <=  0;
endmodule
