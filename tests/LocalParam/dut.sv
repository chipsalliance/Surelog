module top (input wire i, output reg o1, output reg o2);
  assigner #(.invert(0)) asgn0(.inp(i), .out(o1));
  assigner #(.invert(1)) asgn1(.inp(i), .out(o2));
endmodule

module assigner #(parameter invert = 0) (input wire inp, output reg out);
 localparam int do_invert = 0;
 if (!invert)
   assign out = inp;
 if (invert)
   assign out = ~inp;
endmodule

