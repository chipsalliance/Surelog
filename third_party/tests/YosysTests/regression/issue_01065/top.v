module top(input clk);
wire ce = 1'b1;
reg q = 1'b0;
always @(posedge clk)
    if (ce) q <= 1'b0;

(* keep *)
unknown_module u(.i(q));
endmodule
