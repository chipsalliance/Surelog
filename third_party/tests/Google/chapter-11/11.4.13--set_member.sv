/*
:name: set_member
:description: inside operator test
:tags: 11.4.13
*/
module top();

int a;
int b = 12;
localparam c = 5;
localparam d = 7;

initial begin
	a = b inside {c, d};
end

endmodule
