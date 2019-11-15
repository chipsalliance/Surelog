module Add2 (input [1:0] I0, input [1:0] I1, output [1:0] O);
wire  inst0_O;
wire  inst1_CO;
wire  inst2_O;
wire  inst3_CO;
SB_LUT4 #(.LUT_INIT(16'hC33C)) inst0 (.I0(1'b0), .I1(I0[0]), .I2(I1[0]), .I3(1'b0), .O(inst0_O));
SB_CARRY inst1 (.I0(I0[0]), .I1(I1[0]), .CI(1'b0), .CO(inst1_CO));
SB_LUT4 #(.LUT_INIT(16'hC33C)) inst2 (.I0(1'b0), .I1(I0[1]), .I2(I1[1]), .I3(inst1_CO), .O(inst2_O));
SB_CARRY inst3 (.I0(I0[1]), .I1(I1[1]), .CI(inst1_CO), .CO(inst3_CO));
assign O = {inst2_O,inst0_O};
endmodule

module Register2CE (input [1:0] I, output [1:0] O, input  CLK, input  CE);
wire  inst0_Q;
wire  inst1_Q;
//SB_DFFE #(.INIT(1'b0)) inst0 (.C(CLK), .E(CE), .D(I[0]), .Q(inst0_Q));
//SB_DFFE #(.INIT(1'b0)) inst1 (.C(CLK), .E(CE), .D(I[1]), .Q(inst1_Q));
SB_DFFE  inst0 (.C(CLK), .E(CE), .D(I[0]), .Q(inst0_Q));
SB_DFFE  inst1 (.C(CLK), .E(CE), .D(I[1]), .Q(inst1_Q));
assign O = {inst1_Q,inst0_Q};
endmodule

module top (input  CLKIN, input  A, input  CE, output  D1);
wire [1:0] inst0_O;
wire [1:0] inst1_O;
Add2 inst0 (.I0(inst1_O), .I1({1'b0,1'b1}), .O(inst0_O));
Register2CE inst1 (.I(inst0_O), .O(inst1_O), .CLK(CLKIN), .CE(CE));
assign D1 = inst1_O[1];
endmodule
