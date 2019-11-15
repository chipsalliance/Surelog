module top (input [5:0] s, input [6:0] a, output reg y);
  always @* begin
    (* parallel_case *)
    casez (s)
      6'b?????1: y = a[0];
      6'b????1?: y = a[1];
      6'b???1??: y = a[2];
      6'b??1???: y = a[3];
      6'b?1????: y = a[4];
      6'b1?????: y = a[5];
      6'b000000: y = a[6];
    endcase
  end
endmodule
