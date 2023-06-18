
typedef struct packed {logic [3:0] a;} my_struct_packed_t;
module top (
    output my_struct_packed_t out3,
    output wire out4
);
  assign out4   =  (out3 == '1);
endmodule : top
