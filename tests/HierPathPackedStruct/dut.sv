typedef struct packed {  // packed struct, generate bit-sequence with 42 bits
  logic [19:0] foo;
  logic [21:0] bar;
} fourty_two_t;

typedef struct packed {
  fourty_two_t [1:0] pair;  // packed array
} foo_t;

module some_mod(input foo_t a);
  // if ($bits(a.pair) != 2 * 42) begin
  //    $error("whole pair not expected size");
  // end
   if ($bits(a.pair[0]) != 42) begin
      $error("pair element not expected size");
   end
endmodule
