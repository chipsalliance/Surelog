// Bitwise ops on constants wider than 64 bits, and a bitwise XOR at all.
// Caliptra's CALIPTRA_SLAVE_ADDR_WIDTH is
//     $clog2(((BASE ^ MASK) >> (32*n)) & {32{1'b1}})
// with BASE/MASK concatenations of twenty 32-bit literals.  XOR had no case in
// reduceExpr, and get_value() refuses anything wider than 64 bits, so the whole
// expression stayed unresolved: the parameter fell back to the module DEFAULT
// and the leaf's generate picked the wrong arm.
module leaf #(parameter AW = 8) (input wire [AW-1:0] a, output wire [AW-1:0] y);
  generate if (AW > 12) begin : WIDE
    assign y = { a[AW-1:12], 12'h0 };
  end else begin : NARROW
    assign y = a;
  end endgenerate
endmodule

module dut
  #(// XOR of two 64-bit concatenations, shifted and masked by a replication: 17
    parameter W1 = $clog2(((({32'h0000_0000, 32'h1002_8000} ^
                             {32'h0001_7FFF, 32'h1002_FFFF}) >> (32*1)) &
                           {32{1'b1}})),
    // the same shape on a constant wider than 64 bits: 19
    parameter W2 = $clog2((320'h0007ffff_00000000 >> (32*1)) & {32{1'b1}}),
    // a narrow control: 4
    parameter W3 = $clog2({4{1'b1}}))
  (input  wire [W1-1:0] a1, output wire [W1-1:0] y1,
   input  wire [W2-1:0] a2, output wire [W2-1:0] y2,
   input  wire [W3-1:0] a3, output wire [W3-1:0] y3);
  leaf #(.AW(W1)) u1 (.a(a1), .y(y1));   // WIDE
  leaf #(.AW(W2)) u2 (.a(a2), .y(y2));   // WIDE
  leaf #(.AW(W3)) u3 (.a(a3), .y(y3));   // NARROW
endmodule
