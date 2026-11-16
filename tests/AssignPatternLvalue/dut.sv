// IEEE 1800-2023 10.8: an assignment pattern as the TARGET of an assignment
// unpacks an unpacked struct (or array) into its members.
module dut(input  logic [7:0] a, input logic [3:0] b, input logic c,
           output logic [7:0] x, output logic [3:0] y, output logic z,
           output logic [7:0] p, q);
  typedef struct { logic [7:0] f; logic [3:0] g; logic h; } s_t;
  s_t s;
  logic [7:0] arr [2];
  always_comb begin
    s = '{a ^ 8'h5a, b + 4'd1, ~c};
    '{x, y, z} = s;
    arr = '{a, {b, b}};
    '{p, q} = arr;
  end
endmodule
