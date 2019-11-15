/*
:name: program_construct
:description: program construct test
:should_fail: 0
:tags: 24.3
:type: simulation parsing
*/
module top();

program prog(input wire a, input wire b);
	initial $display(":assert: (%d == %d)", a, b);
endprogram

wire w = 1;

initial begin
	prog p(w, w);
end

endmodule
