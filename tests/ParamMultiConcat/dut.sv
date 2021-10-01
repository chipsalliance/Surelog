module dut
#(
   parameter int Width
) (
   input [Width-1:0] wmask_i
);
endmodule

module top;
   parameter int Width = 16;
   parameter int EccWidth = 3;
parameter int BBB = {Width+EccWidth{1'b1}};
   dut #(
      .Width(Width + EccWidth)
   ) u_dut (
      .wmask_i({Width + EccWidth{1'b1}})
   );
endmodule // top

