module dut ();
        test #(
                .Width(32),
                .DataBitsPerMask(8)
        ) t ();
endmodule

module test #(
parameter  int Width           = 32,
parameter  int DataBitsPerMask = 2
) ();
        localparam int MaskWidth = Width / DataBitsPerMask;

generate 
   for (i = 0; i < MaskWidth; i++) begin
      G1 u();
   end
endgenerate 

endmodule

