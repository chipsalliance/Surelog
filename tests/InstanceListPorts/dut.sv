// A comma-separated instance list: ONE instantiation statement, two
// hierarchical instances with their own port connections.  Elaboration used
// to bind the port actuals of the FIRST instance to every instance of the
// list (u2 read x1 / drove y1).
module child #(parameter W = 4) (input logic [W-1:0] a, output logic [W-1:0] y);
   assign y = ~a;
endmodule
module top (input logic [3:0] x1, input logic [3:0] x2, output logic [3:0] y1, output logic [3:0] y2);
   child #(4) u1 (.a(x1), .y(y1)), u2 (.a(x2), .y(y2));
endmodule
