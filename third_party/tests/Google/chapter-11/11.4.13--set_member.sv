/*
:name: set_member
:description: inside operator test
:should_fail: 0
:tags: 11.4.13
*/
module top();

int a;
int b = 12;
int c = 5;
int d = 7;

initial begin
	a = b inside {c, d};
end

endmodule
