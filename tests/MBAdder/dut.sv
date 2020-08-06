module MultibitAdder(a,b,cin,sum,cout);
	input [3:0] a,b;
	input cin;
	output [3:0]sum;
	output cout;
	assign {cout,sum}=a+b+cin;
endmodule

