(* top *)
module rotate_3_var_len (input clk, input [1:0] l, output q);
reg [2:0] r;
initial r = 3'b101;
always @(posedge clk)
    r <= {r[1:0], r[2]};
assign q = r[l];
endmodule

`ifndef _AUTOTB
module __test ;
    wire [4095:0] assert_area = "cd rotate_3_var_len; select t:SRL* -assert-count 0; select t:FD* -assert-count 3";
endmodule
`endif
