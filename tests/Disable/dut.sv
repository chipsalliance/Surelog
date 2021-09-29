module top;
   initial begin
      forever begin : loop
         disable loop;
         disable fork;
      end
   end
endmodule // top
