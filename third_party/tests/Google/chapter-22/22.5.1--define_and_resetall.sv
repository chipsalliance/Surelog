/*
:name: 22.5.1--define_and_resetall
:description: The text macro facility is not affected by the compiler directive `resetall
:tags: 22.5.1
:type: preprocessing simulation
*/
`define SOMESTRING "somestring"
`resetall

module top ();
initial begin
       	$display(":assert:('%s' == '%s')", `SOMESTRING, "somestring");
end
endmodule
