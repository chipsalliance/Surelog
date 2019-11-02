(* top *)
module rotate_3 (input clk, output q);
reg [2:0] r;
initial r = 3'b101;
always @(posedge clk)
    r <= {r[1:0], r[2]};
assign q = r[2];
endmodule

`ifndef _AUTOTB
module __test ;
    wire [4095:0] assert_area = "cd rotate_3; select t:SRL* -assert-count 1; select t:FD* -assert-none";
endmodule
`endif
