module top;
	clocking mem @(clock);
	input instruction = { opcode, regA, regB[3:1] };
	endclocking
	
	
	program test(
		input phi1, input [15:0] data, output logic write,
		input phi2, inout [8:1] cmd, input enable
	);
	reg [8:1] cmd_reg;
	clocking cd1 @(posedge phi1);
		input data;
		output write;
		input state = top.cpu1.state;
	endclocking
	
	clocking cd2 @(posedge phi2);
		input #2 output #4ps cmd;
		input enable;
	endclocking
	initial begin
	end
	
	assign cmd = enable ? cmd_reg: 'x;
	endprogram
endmodule
