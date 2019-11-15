module top(a,z);
   input [7:0] a;
   output [7:0] z;
   parameter pos = 1;

   assign z = ff(a);

   function [7:0] ff;
      parameter pos2 = pos + 1;
      input [7:0] arg1;
      begin
        ff = arg1[pos2:0];
      end
   endfunction
endmodule
