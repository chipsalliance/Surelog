(* top *)
module rotate_7_fdre_param (input clk, output q);
wire [6:0] r;

FDRE #(.INIT(1'b1)) r0 (.C(clk), .CE(1'b1), .D(r[6]), .R(1'b0), .Q(r[0]));
FDRE #(.INIT(1'b0)) r1 (.C(clk), .CE(1'b1), .D(r[0]), .R(1'b0), .Q(r[1]));
FDRE #(.INIT(1'b0)) r2 (.C(clk), .CE(1'b1), .D(r[1]), .R(1'b0), .Q(r[2]));
FDRE #(.INIT(1'b1), .IS_C_INVERTED(1)) r3 (.C(clk), .CE(1'b1), .D(r[2]), .R(reset), .Q(r[3]));
FDRE #(.INIT(1'b0)) r4 (.C(clk), .CE(1'b1), .D(r[3]), .R(1'b0), .Q(r[4]));
FDRE #(.INIT(1'b0)) r5 (.C(clk), .CE(1'b1), .D(r[4]), .R(1'b0), .Q(r[5]));
FDRE #(.INIT(1'b0)) r6 (.C(clk), .CE(1'b1), .D(r[5]), .R(1'b0), .Q(r[6]));

assign q = r[6];
endmodule

`ifndef _AUTOTB
module __test ;
    wire [4095:0] assert_area = "cd rotate_7_fdre_param; select t:SRL* -assert-count 2; select t:FD* -assert-count 1";
endmodule
`endif
