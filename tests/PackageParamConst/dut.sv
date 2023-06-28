package pkg;
   parameter logic [3:0] A = 4'hF;
endpackage

module top(output a);
   assign a = pkg::A[0];
endmodule

