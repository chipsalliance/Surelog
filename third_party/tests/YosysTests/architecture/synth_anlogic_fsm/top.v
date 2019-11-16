module FSM ( clk,rst, en, ls, rs, stop, busy, finish);
	input wire clk;
	input wire rst;
	input wire en;
	input wire ls;
	input wire rs;

	output wire stop;
	output wire busy;
	output wire finish;

	//typedef enum logic [3:0] {S0, S1, S2, S3, S4, S5, S6, S7, S8, S9, S10, S11, S12, S13, S14} sts;
	
    parameter S0 = 4'b0000, S1 = 4'b0001, S2 = 4'b0010, S3 = 4'b0011, S4 = 4'b0100, S5 = 4'b0101, S6 = 4'b0110, S7 = 4'b0111, S8 = 4'b1000, S9 = 4'b1001, S10 = 4'b1010, S11 = 4'b1011, S12 = 4'b1100, S13 = 4'b1101, S14 = 4'b1110;
	
	reg [3:0] ns, st;

	reg [2:0] count;


	always @(posedge clk)
	begin : CurrstProc
		if (rst)
			st <= S0;
		else
			st <= ns;
	end

	always @*
	begin : NextstProc
		ns = st;
		case (st)
			S0: ns = S1;
			S1: ns = S2;
			S2:
				if (rs == 1'b1)
					ns = S3;
				else
					ns = S4;
			S3: ns = S1;
			S4: if (count > 7)
					ns = S10;
				else
					ns = S5;
			S5: if (ls == 1'b0)
					ns = S6;
				else
					ns = S3;
			S6:
				if (ls == 1'b1)
					ns = S7;
				else
					ns = S8;
			S7:
				if (ls == 1'b1 && rs == 1'b1)
					ns = S5;
				else
					ns = S13;
			S8: ns = S9;
			S9: ns = S8;
			S10:
				if (ls == 1'b1 || rs == 1'b1)
					ns = S11;
				else
					ns = S4;
			S11: ns = S12;
			S12: ns = S10;
			S13: ;
			default: ns = S0;
		endcase;
	end
	
	always @(posedge clk)
		if(~rst)
			count <= 0;
		else
		begin
			if(st == S4)
				if (count > 7)
					count <= 0;
				else
					count <= count + 1;
		end

	//FSM outputs (combinatorial)
	assign stop   = (st == S3 || st == S12) ? 1'b1 : 1'b0;
	assign finish = (st == S13) ? 1'b1 : 1'b0;
	assign busy   = (st == S8 || st == S9) ? 1'b1 : 1'b0;

endmodule


module top (
input clk,
input rst,
input en,
input a,
input b,
output s,
output bs,
output f
);

FSM u_FSM ( .clk(clk),
            .rst(rst), 
            .en(en), 
            .ls(a), 
            .rs(b), 
            .stop(s), 
            .busy(bs), 
            .finish(f));

endmodule
