module RAM256X8(B1ADDR, B1DATA, CLK3, A1ADDR, A1DATA, A1EN, CLK2);
	parameter CLKPOL2 = 1;
	parameter CLKPOL3 = 1;
	parameter TRANSP3 = 1;

	input CLK2;
	input CLK3;

	input [7:0] A1ADDR;
	input [7:0] A1DATA;
	input A1EN;

	input [7:0] B1ADDR;
	output [7:0] B1DATA;

	wire c2 = CLK2 == CLKPOL2;
	wire c3 = CLK3 == CLKPOL3;

	reg [7:0] memory [0:255];
	reg [7:0] b1_buffer;

	always @(posedge c2)
		if (A1EN) memory[A1ADDR] <= A1DATA;

	always @(posedge c3)
		b1_buffer <= TRANSP3 ? B1ADDR : memory[B1ADDR];

	assign B1DATA = TRANSP3 ? memory[b1_buffer] : b1_buffer;
endmodule
