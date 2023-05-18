/*
module static_size (
input wire [ 7:0] in7,
output wire [15:0] out7
);
assign out7 = {{8{2'(1'b1)}}, in7};
endmodule
*/

module static_size_casting (
     output wire [ 7:0] out1,
     output wire [ 7:0] out2,
     output wire [15:0] out3,
    output wire [15:0] out4,
     output wire [15:0] out5,
    output wire [15:0] out6
);

  // 8-bit wide outputs.
  assign out1 = 1 << 15;  // Expected 8'b00000000; OK
  assign out2 = 8'(1 << 15);  // Expected 8'b00000000; OK

  // 16-bit wide outputs.
  assign out3 = 1 << 15;  // Expected 16'b1000000000000000; OK
  assign out4 = 8'(1 << 15);  // Expected 16'b0000000000000000; NOT OK
  assign out5 = 16'(8'(1 << 15));  // Expected 16'b0000000000000000; NOT OK
  assign out6 = {8{2'(1'b1)}};  // Expected 16'b0101010101010101; NOT OK

endmodule : static_size_casting