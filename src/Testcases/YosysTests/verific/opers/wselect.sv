module top (input [4:0] s, input [2:0] a, b, c, d, e, output reg [2:0] y);
  always @* begin
    (* parallel_case, full_case *)
    casez (s)
      5'b????1: y = a;
      5'b???1?: y = b;
      5'b??1??: y = c;
      5'b?1???: y = d;
      5'b1????: y = e;
    endcase
  end
endmodule
