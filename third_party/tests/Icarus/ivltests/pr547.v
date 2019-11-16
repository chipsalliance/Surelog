module top;
   reg [9:0] a;
   reg b;
 
   initial begin
      a = 10'h3ff;
      b = a[15];
      $display("A = %h, b = %b", a, b);
   end // initial begin
endmodule // top 
