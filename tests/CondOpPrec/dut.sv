module GOOD();

endmodule

module top #(
  parameter  int Width = 16
) (
   output logic o
);
  localparam int ParWidth = (Width <=  26) ? 6 :
                            (Width <= 120) ? 7 : 8;

  if (ParWidth == 6) begin
     GOOD good();
  end

endmodule // top
