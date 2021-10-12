module foo(
    input clk,
    output out
);
import prim_util_pkg::vbits;
logic [vbits(4)-1:0] a;
always @(posedge clk) begin
    a <= a + 1'b1;
end
assign out = a[0];
endmodule // foo
