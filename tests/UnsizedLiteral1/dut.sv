
module counter ( output wire [3:0] out );
 
  assign out = '1; // Should be 4'b1

endmodule


/*
typedef struct packed {logic [3:0] a;} my_struct_packed_t;

module unsized_single_bit_1 (
    output wire [3:0] out1,
    output wire out2,
    output my_struct_packed_t out3,
    output wire out4
);

  // out1 should be 4'b1111
  assign out1   = '1;

  // out2 should be 1'b1
  assign out2   = (out1 == 4'b1111);

  // out3 should be 4'b1111
  assign out3.a = '1;

  // out4 should be 1'b1
  assign out4   = (out3 == '1);

endmodule : unsized_single_bit_1


  */