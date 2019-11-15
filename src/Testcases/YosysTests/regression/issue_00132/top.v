module submod(input [7:0] a, output [7:0] y);
  parameter integer increment = 0;
  initial begin
    if (increment == 0) begin
      $display("increment parameter must have a non-zero value!");
      //$stop;
    end
  end
  assign y = a + increment;
endmodule

module top(input [7:0] a, output [7:0] y);
  parameter integer incr = 0;
  submod #(incr) submod_instance (a, y);
endmodule
