(* top *)
module rotate_3_fdre (input clk, output q);
wire [2:0] r;
FDRE #(.INIT(1'b1)) r0 (.C(clk), .CE(1'b1), .D(r[2]), .R(1'b0), .Q(r[0]));
FDRE #(.INIT(1'b0)) r1 (.C(clk), .CE(1'b1), .D(r[0]),           .Q(r[1]));
FDRE #(.INIT(1'b0)) r2 (.C(clk), .CE(1'b1), .D(r[1]), .R(1'b0), .Q(r[2]));
assign q = r[2];
endmodule

`ifndef _AUTOTB
module __test ;
    wire [4095:0] assert_area = "cd rotate_3_fdre; select t:SRL* -assert-count 1; select t:FD* -assert-none";
endmodule
`endif
