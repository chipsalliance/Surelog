module top;
   prim_flop #(
      .Width(22)
   ) u_prim_flop();
endmodule

module prim_flop;
   parameter int Width = 1;
   parameter logic [Width-1:0] ResetValue = Width;
endmodule

