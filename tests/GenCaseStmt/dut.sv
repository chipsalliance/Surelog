

module GOOD();
endmodule

module top();
  parameter bit unsigned x_1b0 = 1'b0;
  parameter bit signed x_1sb0 = 1'sb0;
  parameter bit signed x_1sb1 = 1'sb1;
  parameter logic signed [1:0] x_2sb11 = 2'sb11;

  case (x_2sb11)
    2'b?1: BAD u2();
    default: GOOD u3();
  endcase

  // Mix signed and unsigned
  case (x_2sb11)
    x_1b0:  BAD u1();
    x_1sb1: BAD u2();
    default: GOOD u3();
  endcase

  case (x_2sb11)
    x_1sb0:  BAD u1();
    x_1sb1: GOOD u2();
    default: BAD u3();
  endcase

endmodule

