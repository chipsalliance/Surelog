/*
:name: 22.5.1--define_and_resetall
:description: The text macro facility is not affected by the compiler directive `resetall
:should_fail: 0
:tags: 22.5.1
:type: preprocessing simulation
*/
`define FOUR 5
`define SOMESTRING "somestring"
`resetall
`define FOUR 4

module top ();
initial begin
        $display(":assert:(FOUR == 4)");
       	$display(":assert:('%s' == '%s')", SOMESTRING, "somestring");
end
endmodule
