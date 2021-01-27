module assigner #(parameter invert = 0) ();
  if (!invert)
    assign out = inp;
  if (invert)
    assign out = ~inp;
endmodule

module middleman #(parameter invert = 0) ();
   assigner #(.invert(invert)) asgn();
endmodule
