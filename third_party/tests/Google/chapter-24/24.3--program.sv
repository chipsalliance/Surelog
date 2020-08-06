/*
:name: program_construct
:description: program construct test
:tags: 24.3
:type: simulation parsing
*/
program prog(input wire a, input wire b);
	initial $display(":assert: (%d == %d)", a, b);
endprogram

module top();

   wire a = 1;
   wire b = 1;

   prog p(a, b);

endmodule
