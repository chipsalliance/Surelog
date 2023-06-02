
module GOOD();
endmodule

module top();
  parameter bit unsigned x_1b0 = 1'b0;
  parameter bit signed x_1sb0 = 1'sb0;
  parameter bit signed x_1sb1 = 1'sb1;
  parameter logic signed [1:0] x_2sb11 = 2'sb11;

  case (x_2sb11)
    x_1sb1: begin: tag1
      GOOD u2();
    end
    default: BAD u3();
  endcase

  
endmodule